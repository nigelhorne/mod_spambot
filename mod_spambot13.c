/*
 *  Copyright (C) 2005 Nigel Horne <njh@bandsman.co.uk>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 *  MA 02110-1301, USA.
 *
 * mod_spambot for Apache 1.3
 * Stop spambots from digging around your site.
 *
 * To build and install:
 *	/usr/sbin/apxs -i -a -c mod_spambot13.c
 *
 * TODO: Option to automagically add the IP address to "deny from" in httpd.conf
 *	Need to work out where httpd.conf is - and what about virtual servers?
 *	We won't have write permission to TCPwrappers (/etc/hosts.deny)
 * TODO: Add IP range support to SpamBotWhiteList.
 * TODO: Set HTTP_REFERER (if empty) to the requested URI so that errorDocument
 *	can pick it up (if that's possible with Apache)
 * TODO: Look at the if-modified-since header. If that's present does it mean
 *	it's a nice bot that we should allow?
 * TODO: Support SpamBotAddSuffix with no suffixes
 * TODO: Support via mime type as well as suffix (see MIMETYPE ifdef). This
 *	will need a complete rewrite since it would mean deciding to deny
 *	access only after the output has been assembled, which wouldn't be
 *	very efficient so I'm not likely to do it
 * TODO: Improved handing of vhosts, and test .htaccess works
 * TODO: Add sanity checks that SpamBotTriggerTime <= SpamBotReuseTime,
 *		and that SpamBotMinIdleTime <= SpamBotReuseTime.
 * TODO: Instead of redirecting, send the contents of SpamBotRedirectPath
 *		from here, that should give us greater control over the HTTP
 *		status code and allow us to send SpamBotDenyCode and allow us
 *		to implement a bait machine
 * TODO: Implement sendmail bad_rcpt_throttle type idea
 * TODO: Only send one email per throttling
 */
#include <unistd.h>
#include <stdio.h>
#include <time.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <pthread.h>

#define	CORE_PRIVATE

#include <httpd.h>
#include <http_config.h>
#include <http_core.h>
#include <http_protocol.h>
#include <http_core.h>
#include <http_request.h>
#include <http_log.h>
#include <util_md5.h>

/*#define	MOD_SPAMBOT_VERSION	"0.47"*/
#define	MOD_SPAMBOT_VERSION	"devel-100106"

module MODULE_VAR_EXPORT spambot_module;

/*
 * The dbfile is a series of connection records. Held in a file rather than
 * a shared memory area since that makes it easier to implement per-directory
 * options
 *
 * FIXME: Currently the dbfile needs to be truncated manually before startup
 *	when the default name (/tmp/spambot.db) is used
 */
#ifdef	DARWIN	/* also needed for older Linux e.g. Red Hat 5.2 */
typedef	unsigned	int	in_addr_t;
#endif

/* track by mod_usertrack, and if that fails use ipaddr */
typedef struct connection {
	char	*usertrack;	/* RFC1321 (MD5) digest of the cookie */
	in_addr_t	ipaddr;
	unsigned	long	count;
	time_t	timestamp;
	int	emailSent;	/*
				 * stops follow up emails when a client keeps
				 * blitzing us
				 */
} connection;

/*
 * If you change these, remember to change the help messages in spambot_cmds
 */
#define	MAGIC	0xdeadbeef
#define	DEFAULT_TRIGGER_LEVEL	100
#define	DEFAULT_TRIGGER_TIME	3600
#define	DEFAULT_REUSE_TIME	600
#define	DEFAULT_DBNAME		"/tmp/spambot.db"
#define	DEFAULT_DENY_CODE	HTTP_FORBIDDEN
#define	DEFAULT_USERTRACK_NAME	"Apache"	/* see mod_usertrack.c */

#ifndef NAME_MAX	/* e.g. Linux */
#define	NAME_MAX	 MAXNAMELEN	/* e.g. Solaris */
#endif

#ifndef	INET_ADDRSTRLEN
#define	INET_ADDRSTRLEN	16
#endif

#define	SENDMAIL_BIN	"/usr/sbin/sendmail"

typedef struct spambotConfig {
	int	enabled;
	int	magic;
	int	trigger_level;
	int	trigger_time;
	int	reuse_time;
	int	deny_code;	/* default 403 */
	int	min_idle;
	char	*cookie_name;	/* mod_usertrack */
	char	dbname[NAME_MAX + 1];
	char	dbgfile[NAME_MAX + 1];
	char	redirect[NAME_MAX + 1];
	char	*redirect_type;	/* MIME type of the redirect file */
	char	dir[NAME_MAX + 1];
	int	sendemail;
} spambotConfig;

#define	MAKEMASK(bits)	((uint32_t)(0xffffffff << (bits)))

typedef struct whitelist {
	in_addr_t	ipaddr;	/* e.g. 192.168.0.0 */
	in_addr_t	mask;	/* e.g. 16, as in 192.168.0.0/16 */
	struct whitelist *next;
} whitelist;

/*
 * FIXME: this is per server, should be per directory
 */
static	whitelist	*whitehead, *whitelast;

typedef	struct	suffix {
	char	*suffix;
	struct	suffix	*next;
} suffix;

static	suffix	*suffixhead, *suffixlast;

static	pthread_mutex_t	sleeper_mutex = PTHREAD_MUTEX_INITIALIZER;
static	pthread_cond_t	sleeper_cond = PTHREAD_COND_INITIALIZER;

static	int	server_timeout;

static	void	waitfor(spambotConfig *config, int nsec, const char *ip, FILE *debug, const server_rec *s, const char *cookieval);
static	const	char	*mime(const char *filename);
static	void	sendblockedemail(const spambotConfig *config, const server_rec *s, const char *cookieval, const char *name, const char *ip);
static	void	sendwaitemail(const spambotConfig *config, const server_rec *s, const char *cookieval, const char *ip, int seconds);

static void
spambot_server_init(server_rec *c, pool *p)
{
	ap_add_version_component("mod_spambot/" MOD_SPAMBOT_VERSION);
}

static void *
create_spambot_server(pool *p, server_rec *s)
{
	spambotConfig *ret = (spambotConfig *)ap_pcalloc(p, sizeof(struct spambotConfig));

	if(ret)
		ret->magic = MAGIC;
	server_timeout = (int)(s->timeout / 1000000);

	return ret;
}

static void *
create_spambot_dir(pool *p, char *dir)
{
	spambotConfig *ret = (spambotConfig *)ap_pcalloc(p, sizeof(struct spambotConfig));

	if(ret) {
		if(dir)
			strcpy(ret->dir, dir);

		ret->magic = MAGIC;
	}

	return ret;
}

static void *
merge_spambot_dir(pool *p, void *base, void *add)
{
	const char *mime_type;
	spambotConfig *b = (spambotConfig *)base;
	spambotConfig *a = (spambotConfig *)add;
	spambotConfig *ret = ap_palloc(p, sizeof(struct spambotConfig));
	FILE *debug;

	if(ret == NULL)
		return NULL;

	if(a->dbgfile[0])
		debug = fopen(a->dbgfile, "a");
	else if(b->dbgfile[0])
		debug = fopen(b->dbgfile, "a");
	else
		debug = NULL;

	if(debug) {
		fprintf(debug, "merge_spambot_dir: b->dir '%s', a->dir '%s'\n", b->dir, a->dir);
		fprintf(debug, "merge_spambot_dir: b->enabled %d, a->enabled %d\n", b->enabled, a->enabled);
		fprintf(debug, "merge_spambot_dir: b->dbname '%s', a->dbname '%s'\n", b->dbname, a->dbname);
		fprintf(debug, "merge_spambot_dir: b->dbgfile '%s', a->dbgfile '%s'\n", b->dbgfile, a->dbgfile);
		fclose(debug);
	}

	memcpy(ret, b, sizeof(spambotConfig));
	if(b->cookie_name)
		ret->cookie_name = ap_pstrdup(p, b->cookie_name);

	strcpy(ret->dir, a->dir);

	if(a->trigger_level != DEFAULT_TRIGGER_LEVEL)
		ret->trigger_level = a->trigger_level;
	if(ret->trigger_level == 0)
		ret->trigger_level = DEFAULT_TRIGGER_LEVEL;

	if(a->trigger_time != DEFAULT_TRIGGER_TIME)
		ret->trigger_time = a->trigger_time;
	if(ret->trigger_time == 0)
		ret->trigger_time = DEFAULT_TRIGGER_TIME;

	if(a->min_idle != 0)
		ret->min_idle = a->min_idle;

	if(a->reuse_time != DEFAULT_REUSE_TIME)
		ret->reuse_time = a->reuse_time;
	if(ret->reuse_time == 0)
		ret->reuse_time = DEFAULT_REUSE_TIME;

	if(strcmp(a->dbname, DEFAULT_DBNAME) != 0)
		strcpy(ret->dbname, a->dbname);
	if(ret->dbname[0] == '\0')
		strcpy(ret->dbname, DEFAULT_DBNAME);

	if(a->dbgfile[0])
		strcpy(ret->dbgfile, a->dbgfile);

	if(a->deny_code != DEFAULT_DENY_CODE)
		ret->deny_code = a->deny_code;
	if(ret->deny_code == 0)
		ret->deny_code = DEFAULT_DENY_CODE;

	if(a->redirect[0])
		strcpy(ret->redirect, a->redirect);
	ret->redirect_type = NULL;
	if(ret->redirect[0]) {
		/*if(ret->deny_code == DEFAULT_DENY_CODE)
			ret->deny_code = HTTP_MOVED_TEMPORARILY;*/
		mime_type = mime(ret->redirect);
		if(mime_type)
			ret->redirect_type = ap_pstrdup(p, mime_type);
	}

	ret->enabled = a->enabled;

	return ret;
}

static const char *
spambot_on(cmd_parms *cmd, void *c, int arg)
{
	spambotConfig *config;

	if(c == NULL)
		return "spambot_on: can't get config structure";

	config = (spambotConfig *)c;
	if(config->magic != MAGIC)
		return "spambot_on: bad magic - sanity check failed";

	config->enabled = arg;
	if(arg) {
		/* Load some defaults */
		strcpy(config->dbname, DEFAULT_DBNAME);
		config->trigger_level = DEFAULT_TRIGGER_LEVEL;
		config->trigger_time = DEFAULT_TRIGGER_TIME;
		config->reuse_time = DEFAULT_REUSE_TIME;
		config->deny_code = DEFAULT_DENY_CODE;
		config->cookie_name = ap_pstrdup(cmd->pool, DEFAULT_USERTRACK_NAME);
		config->min_idle = 0;
		config->dbgfile[0] = '\0';
		config->redirect[0] = '\0';
		config->redirect_type = NULL;
	}

	return NULL;
}

/*
 * FIXME: On first start up, the database (and debug files) are owned by root
 *	not the apache user, you need to chown by hand
 */
static const char *
set_db_file(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		const char *filename = ap_server_root_relative(cmd->pool, (char *)arg);
		int fd;
		spambotConfig *config = (spambotConfig *)c;

		if(filename == NULL)
			filename = arg;
		fd = open(filename, O_CREAT|O_TRUNC, 0600);
		if(fd < 0) {
			perror(filename);
			return "Failed to create SpamBotDatabaseFile";
		}
		close(fd);
		strcpy(config->dbname, filename);
	}
	return NULL;
}

static const char *
set_dbg_file(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		const char *filename = ap_server_root_relative(cmd->pool, (char *)arg);
		spambotConfig *config = (spambotConfig *)c;
		FILE *debug;

		if(filename == NULL)
			filename = arg;
		debug = fopen(filename, "a");

		if(debug == NULL)
			return "Failed to create SpamBotDebugFile";

		fputs("----------------------\n", debug);
		fclose(debug);
		strcpy(config->dbgfile, filename);
	}
	return NULL;
}

static const char *
set_trigger_level(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		spambotConfig *config = (spambotConfig *)c;

		config->trigger_level = atoi(arg);
		if(config->trigger_level <= 0)
			fprintf(stderr, "Silly trigger level %d\n", config->trigger_level);
	}
	return NULL;
}

static const char *
set_trigger_time(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		spambotConfig *config = (spambotConfig *)c;

		config->trigger_time = atoi(arg);
		if(config->trigger_time <= 0)
			fprintf(stderr, "Silly trigger time %d\n", config->trigger_time);
	}
	return NULL;
}

static const char *
set_reuse_time(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		spambotConfig *config = (spambotConfig *)c;

		config->reuse_time = atoi(arg);
		if(config->reuse_time <= 0) {
			fprintf(stderr, "Silly re-use time %d\n", config->reuse_time);
			config->reuse_time = DEFAULT_REUSE_TIME;
		}
	}
	return NULL;
}

static const char *
set_deny_code(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		spambotConfig *config = (spambotConfig *)c;

		config->deny_code = atoi(arg);
		if(config->deny_code <= 0) {
			fprintf(stderr, "Silly deny code %d\n", config->deny_code);
			config->deny_code = DEFAULT_DENY_CODE;
		}
	}
	return NULL;
}

static const char *
set_min_idle(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		spambotConfig *config = (spambotConfig *)c;

		config->min_idle = atoi(arg);
		if(config->min_idle < 0) {
			fprintf(stderr, "Silly min idle value %d\n", config->min_idle);
			config->min_idle = 0;
		} else if(server_timeout && (config->min_idle > server_timeout)) {
			fprintf(stderr, "min idle time (%d) cannot be greater than the server's timeout (%d)\n", config->min_idle, server_timeout);
			config->min_idle = 0;
		}
	}
	return NULL;
}

static const char *
set_redirect_path(cmd_parms *cmd, void *c, const char *arg)
{
	if(c && arg) {
		const char *mime_type;

		spambotConfig *config = (spambotConfig *)c;

		/*if((strcmp(arg, "honeypot") != 0) && !ap_is_url(arg))
			return "Spamredirect path to non-URL";*/

		strcpy(config->redirect, arg);

		mime_type = mime(arg);
		if(mime_type)
			config->redirect_type = ap_pstrdup(cmd->pool, mime_type);
	}

	return NULL;
}

static const char *
add_to_whitelist(cmd_parms *cmd, void *c, const char *arg)
{
	in_addr_t ipaddr, mask;
	char *ptr;
	spambotConfig *config;

	if(c == NULL)
		return NULL;
	if(arg == NULL)
		return NULL;

	config = (spambotConfig *)c;
	if(config->dbgfile[0]) {
		FILE *debug = fopen(config->dbgfile, "a");

		if(debug) {
			fprintf(debug, "whitelist %s\n", arg);
			fclose(debug);
		}
	}

	ptr = strchr(arg, '/');
	if(ptr) {
		char inet[INET_ADDRSTRLEN + 1];

		mask = MAKEMASK((in_addr_t)atol(++ptr));

		strncpy(inet, arg, sizeof(inet) - 1);
		inet[sizeof(inet) - 1] = '\0';	/* Ensure NUL termination */
		ptr = strchr(inet, '/');
		if(ptr)
			*ptr = '\0';
		ipaddr = ntohl(inet_addr(inet));
	} else {
		mask = (in_addr_t)0;
		ipaddr = ntohl(inet_addr(arg));
	}

	if(ipaddr == INADDR_NONE)
		return "Invalid IPv4 address";

	if(whitehead == NULL)
		whitehead = whitelast = ap_palloc(cmd->pool, sizeof(struct whitelist));
	else {
		whitelast->next = ap_palloc(cmd->pool, sizeof(struct whitelist));
		whitelast = whitelast->next;
	}
	if(whitelast == NULL)
		return "Out of memory";

	whitelast->next = NULL;
	whitelast->ipaddr = ipaddr;
	whitelast->mask = mask;

	return NULL;
}

static const char *
add_to_suffix(cmd_parms *cmd, void *c, const char *arg)
{
	spambotConfig *config;

	if(c == NULL)
		return NULL;
	if(arg == NULL)
		return NULL;

	config = (spambotConfig *)c;
	if(config->dbgfile[0]) {
		FILE *debug = fopen(config->dbgfile, "a");

		if(debug) {
			fprintf(debug, "suffix %s\n", arg);
			fclose(debug);
		}
	}

	if(suffixhead == NULL)
		suffixhead = suffixlast = ap_palloc(cmd->pool, sizeof(struct suffix));
	else {
		suffixlast->next = ap_palloc(cmd->pool, sizeof(struct suffix));
		suffixlast = suffixlast->next;
	}
	if(suffixlast == NULL)
		return "Out of memory";

	suffixlast->next = NULL;
	suffixlast->suffix = ap_pstrdup(cmd->pool, arg);

	return NULL;
}

static const char *
set_cookie_name(cmd_parms *cmd, void *c, const char *arg)
{
	spambotConfig *config;

	if(c == NULL)
		return NULL;
	if(arg == NULL)
		return NULL;

	config = (spambotConfig *)c;

	config->cookie_name = ap_pstrdup(cmd->pool, arg);

	return NULL;
}

static const char *
set_sendemail(cmd_parms *cmd, void *c, int arg)
{
	spambotConfig *config;

	if(cmd->server->server_admin == NULL)
		return "set_sendemail: You have not set the ServerAdmin in your httpd.conf";

	if(c == NULL)
		return "set_sendemail: can't get config structure";

	config = (spambotConfig *)c;
	if(config->magic != MAGIC)
		return "set_sendemail: bad magic - sanity check failed";

	config->sendemail = arg;

	return NULL;
}

/*
 * Don't match any SpamBotWhiteList IP addresses (IPv4 only)
 *
 * TODO: prune any where timestamp > 24 hours (or some long time)
 * TODO: allow spidername, e.g. Googlebot
 *	ap_table_get(r->headers_in, "User-Agent");
 *	though these can be forged.
 *
 * Pseudocode:
 *	Delete the details of all clients where the last access was more
 *		than both SpamBotReuseTime and SpamBotTriggerTime seconds ago;
 *	IF total number of accesses from this client >= SpamBotTriggerLevel
 *	THEN
 *		increment the number of accesses for this client;
 *		IF last access was less than SpamBotTriggerTime seconds ago
 *		THEN
 *			IF last access was less than SpamBotMinIdleTime seconds ago
 *			THEN
 *				wait until SpamBotMinIdleTime seconds have elpased from last access
 *			FI;
 *			deny the access
 *		FI
 *	ELIF last access was more than SpamBotTriggerTime seconds ago
 *	THEN
 *		reset number of accesses from this client back to 1;
 *		allow the access
 *	ELSE
 *		increment the number of accesses for this client;
 *		IF last access was less than SpamBotMinIdleTime seconds ago
 *		THEN
 *			wait until SpamBotMinIdleTime seconds have elpased from last access
 *		FI;
 *		allow the access
 *	FI
 */
static int
spambot(request_rec *r)
{
	conn_rec *c = r->connection;
	spambotConfig *config;
	connection *connection, *buf;
	time_t now;
	size_t size;
	int found, i, fd, nrec;
	struct stat statb;
	in_addr_t remote;
	const char *ptr, *cookie_header, *cookieval;
	const struct suffix *s;
	char *digest = NULL;
	FILE *debug;
	unsigned int waitlength;
	unsigned long count;

	/*if(!ap_is_initial_req(r))
		return DECLINED;*/

#if	0
	if(strcasecmp(c->ap_auth_type, "Basic") == 0)
		/* Authenticated users can do anything */
		return DECLINED;
#endif

	config = (spambotConfig *)ap_get_module_config(r->per_dir_config, &spambot_module);

	if(config == NULL) {
		ap_log_rerror(APLOG_MARK, APLOG_ERR, r, "no spambot config");
		return DECLINED;
	}
	if(config->magic != MAGIC) {
		ap_log_rerror(APLOG_MARK, APLOG_ERR, r, "spambot consistency check failed");
		return DECLINED;
	}

	if(config->dbgfile[0]) {
		debug = fopen(config->dbgfile, "a");
		if(debug) {
			setlinebuf(debug);
			/* TODO: add the request to this debug statement */
			fprintf(debug, "spambot %s\n", c->remote_ip);
			fprintf(debug, "r->uri %s\n", r->uri);
			fprintf(debug, "r->the_request %s\n", r->the_request);
			if(config->dir[0])
				fprintf(debug, "dir '%s'\n", config->dir);
			/*fprintf(debug, "r->filename %s\n", r->filename);*/
		}
	} else
		debug = NULL;

	if(!config->enabled) {
		if(debug) {
			fputs("Not enabled\n", debug);
			fclose(debug);
		}
		return DECLINED;
	}

	/* Don't count HEAD requests */
	if(strncmp(r->the_request, "HEAD ", 5) == 0) {
		if(debug)
			fclose(debug);
		return DECLINED;
	}

	/*
	 * If we're handling an unauthorisation error return immediately, it
	 * may be one we've just generated, and even if it isn't there's no need
	 * not to pass it back
	 *
	 * TODO: There's still some work to ensure that all cases of URI match
	 * TODO: Also return if HTTP_REFERER is set to the errorDocument
	 */
	if(config->redirect[0]) {
		if(debug)
			fprintf(debug, "redirect %s\n", config->redirect);
		if(strcmp(r->uri, config->redirect) == 0) {
			if(debug)
				fclose(debug);
			return DECLINED;
		}
	} else {
		const char *errorDocument = ap_response_code_string(r,
			ap_index_of_response(config->deny_code));
		const size_t d = errorDocument ? strlen(errorDocument) : 0;
		const size_t u = strlen(r->uri);

		if(errorDocument && (u <= d)) {
			const char *ptr = &errorDocument[d - u];

			if(errorDocument && (strcmp(r->uri, ptr) == 0)) {
				if(debug) {
					fputs("Allow 403 errorDocument to be returned\n", debug);
					fclose(debug);
				}
				return DECLINED;
			}
		}
	}

	ptr = strrchr(r->uri, '.');
	if(ptr == NULL) {
		if(debug)
			fclose(debug);
		return DECLINED;
	}

	ptr++;

	for(s = suffixhead; s; s = s->next)
		if(strcasecmp(ptr, s->suffix) == 0)
			break;

	if(s == NULL) {
		if(debug)
			fclose(debug);
		return DECLINED;
	}

	remote = ntohl(inet_addr(c->remote_ip));
	if(whitehead) {
		const struct whitelist *w;

		/*
		 * FIXME: this linear search will be slow for large sites.
		 * Could sort (using qsort) in decending order by ipaddr, then
		 * either
		 *	Linear search stopping when w->ipaddr < remote; or
		 *	Binary chop search
		 */
		for(w = whitehead; w; w = w->next)
			if(w->mask == (in_addr_t)0) {
				if(w->ipaddr == remote)
					break;
			} else if((w->ipaddr & w->mask) == (remote & w->mask))
				break;

		if(w) {
			if(debug) {
				fprintf(debug, "whitelisted %s\n",
					c->remote_ip);
				fclose(debug);
			}
			return DECLINED;
		}
	}

	/*
	 * Follow users using mod_usertrack if available
	 */
	cookieval = NULL;
	if((cookie_header = ap_table_get(r->headers_in, "Cookie")) != NULL) {
		const char *regexp_string = ap_pstrcat(r->pool, "^",
			config->cookie_name, "=([^;]+)|;[ \t]+",
			config->cookie_name, "=([^;]+)", NULL);
		regex_t *regexp = ap_pregcomp(r->pool, regexp_string, REG_EXTENDED);
		regmatch_t regm[3];

		if(ap_regexec(regexp, cookie_header, 3, regm, 0) == 0) {
			if(regm[1].rm_so != -1)
				cookieval = ap_pregsub(r->pool, "$1",
					cookie_header, 3, regm);
			if(regm[2].rm_so != -1)
				cookieval = ap_pregsub(r->pool, "$2",
					cookie_header, 3, regm);
			if(cookieval) {
				if(debug)
					fprintf(debug, "Found mod_usertrack cookie '%s'\n", cookieval);
				cookieval = ap_pstrdup(r->pool, cookieval);
			}
		}
		ap_pregfree(r->pool, regexp);
		if(cookieval)
			digest = ap_md5(r->pool, (unsigned char *)cookieval);
	}

	if(debug)
		fprintf(debug, "dbname '%s'\n", config->dbname);

	fd = open(config->dbname, O_RDWR);
	if(fd < 0) {
		/* race condition - but not harmful */
		if(errno == ENOENT) {
			fd = open(config->dbname, O_WRONLY|O_CREAT, 0644);
			if(fd < 0) {
				perror(config->dbname);
				ap_log_rerror(APLOG_MARK, APLOG_ERR, r, "couldn't create spambot database, check SpamBotDatabaseFile (%s)", config->dbname);
				if(debug)
					fclose(debug);
				return DECLINED;
			}
		} else {
			ap_log_rerror(APLOG_MARK, APLOG_ERR, r, "couldn't open spambot database, check SpamBotDatabaseFile (%s)", config->dbname);
			perror(config->dbname);
			if(debug)
				fclose(debug);
			return DECLINED;
		}
	}

	if(flock(fd, LOCK_EX) < 0) {
		perror(config->dbname);
		close(fd);
		if(debug)
			fclose(debug);
		return DECLINED;
	}

	if(fstat(fd, &statb) < 0) {
		perror(config->dbname);
		close(fd);
		if(debug)
			fclose(debug);
		return DECLINED;
	}

	size = statb.st_size;

	if(size) {
		buf = connection = (struct connection *)mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
		if(connection == (struct connection *)-1) {
			perror("mmap");
			close(fd);
			if(debug)
				fclose(debug);
			return DECLINED;
		}
	} else
		buf = connection = NULL;

	found = 0;
	nrec = size / sizeof(struct connection);

	time(&now);

	if(size) {
		if(debug)
			fprintf(debug, "size %d nrec %d\n",
				size, size / sizeof(struct connection));

		for(i = 0; i < nrec; i++, connection++)
			if((connection->ipaddr == -1) && cookieval) {
				if(strcmp(connection->usertrack, digest) == 0) {
					if((now - connection->timestamp) < config->trigger_time)
						found = 1;
					break;
				}
			} else if(connection->ipaddr == remote) {
				if((now - connection->timestamp) < config->trigger_time)
					found = 1;
				break;
			}

		if(debug)
			fprintf(debug, "found %d i %d\n", found, i);
	}

	if(!found) {
		struct connection c1;

		if(buf) {
			/*
			 * find an old entry to reuse
			 * TODO: this involves a second scan - would be better
			 *	to combine with the scan above
			 */
			for(i = 0, connection = buf; i < nrec; i++, connection++)
				if((now - connection->timestamp) > config->reuse_time)
					break;
			if(i < nrec) {
				if(debug) {
					fprintf(debug,
						"re-use record %d - not used for %lu seconds\n",
							i, (now - connection->timestamp));
					fclose(debug);
				}
				connection->count = 1;
				connection->timestamp = now;
				if(cookieval) {
					connection->usertrack = ap_pstrdup(r->pool, digest);
					connection->ipaddr = -1;
				} else
					connection->ipaddr = remote;
				connection->emailSent = 0;
				munmap((void *)buf, size);
				close(fd);
				return DECLINED;
			}
			munmap((void *)buf, size);
		}
		if(cookieval) {
			connection->usertrack = ap_pstrdup(r->pool, digest);
			c1.ipaddr = -1;
		} else {
			c1.usertrack = NULL;
			c1.ipaddr = remote;
		}
		c1.count = 1;
		c1.timestamp = now;
		c1.emailSent = 0;
		lseek(fd, 0L, SEEK_END);
		if(write(fd, &c1, sizeof(struct connection)) < 0)
			perror(config->dbname);
		else if(debug)
			fprintf(debug, "new record %s\n", c->remote_ip);

		close(fd);

		if(debug)
			fclose(debug);
		return DECLINED;
	}

	if(connection->count >= config->trigger_level) {
		connection->count++;
		if((now - connection->timestamp) < config->trigger_time) {
			count = connection->count;
#if	0
			char *referer;

			if(apr_env_get(&referer, "HTTP_REFERER", r->pool) == APR_ENOENT) {
				apr_env_set("HTTP_REFERER", r->uri, r->pool);
				if(debug)
					fputs("Set HTTP_REFERER\n", debug);
			}
#endif
			/* Log the first block */
			if(count == config->trigger_level + 1) {
				const char *name;

				/* FIXME: Level should be configurable */
				if(cookieval) {
					ap_log_rerror(APLOG_MARK, APLOG_NOERRNO|APLOG_NOTICE, r, "User %s has been blocked", cookieval);
					name = NULL;
				} else {
					name = ap_get_remote_host(c, r->per_dir_config, REMOTE_NAME);

					if(name)
						ap_log_rerror(APLOG_MARK, APLOG_NOERRNO|APLOG_NOTICE, r, "Site %s has been blocked", name);
					else
						ap_log_rerror(APLOG_MARK, APLOG_NOERRNO|APLOG_NOTICE, r, "%s has been blocked", c->remote_ip);
				}
				if(!connection->emailSent) {
					sendblockedemail(config, r->server, cookieval, name, c->remote_ip);
					connection->emailSent = 1;
				}
			}

			if((now - connection->timestamp) < config->min_idle)
				waitlength = config->min_idle - (now - connection->timestamp);
			else
				waitlength = 0;

			connection->timestamp = now + waitlength;
			munmap((void *)buf, size);
			close(fd);

			if(debug) {
				if(cookieval)
					fprintf(debug, "user %s count %lu - blocked\n", cookieval, count);
				else
					fprintf(debug, "ip %s count %lu - blocked\n", c->remote_ip, count);
				if(config->redirect[0])
					fprintf(debug, "redirect to: '%s' %d\n", config->redirect, config->deny_code);
			}
			if(waitlength)
				waitfor(config, waitlength, c->remote_ip, debug, r->server, cookieval);

			if(debug)
				fclose(debug);

			/* redirect to a different page? */
			if(config->redirect[0]) {
				int rc;
				if(strcasecmp(config->redirect, "honeypot") == 0) {
					/*
					 * TODO: Print the generated email
					 *	address and website to debug
					 * TODO: The mailto should point to
					 *	abuse@ at the ISP of the spambot
					 */
					ap_send_http_header(r);
					r->content_type = "text/html";
					ap_rputs(DOCTYPE_HTML_3_2, r);
					ap_rputs("<HTML>", r);
					ap_rputs("<BODY>", r);
					ap_rprintf(r, "<A HREF=\"mailto:honeypot%lu@w1959.com\">honeypot%lu@w1959.com</A><br />", count, count);
					ap_rprintf(r, "<A HREF=\"next%lu.htm\">don't click here</A>", count);
					ap_rputs("</BODY>", r);
					ap_rputs("</HTML>", r);
					rc = OK;
				} else {
					FILE *fin;
					const char *filename = ap_server_root_relative(r->pool, config->redirect);

					filename = ap_make_full_path(r->pool, ap_document_root(r), filename);
					fin = fopen(filename, "r");

					if(fin) {
						char buffer[BUFSIZ];

						if(config->redirect_type)
							r->content_type = config->redirect_type;
						ap_send_http_header(r);
						while(fgets(buffer, sizeof(buffer), fin) != NULL)
							ap_rputs(buffer, r);
						fclose(fin);

						return config->deny_code;
					}
					ap_log_rerror(APLOG_MARK, APLOG_ERR, r, "Can't open SpamBotRedirectPath %s", filename);

					ap_table_setn(r->headers_out, "Location", config->redirect);
					ap_table_setn(r->headers_out, "URI", config->redirect);
					ap_table_setn(r->headers_out, "Content-Location", config->redirect);
					rc = HTTP_MOVED_TEMPORARILY;
				}
				ap_table_unset(r->headers_out, "Content-Length");
				ap_table_unset(r->headers_out, "Content-Type");
				if(cookieval)
					/* already strduped so this is safe */
					ap_table_addn(r->headers_out, "Set-Cookie", cookieval);
				return rc;
			}
			return config->deny_code;
		}
	} else if((now - connection->timestamp) > config->trigger_time)
		connection->count = 1;
	else
		connection->count++;

	if((connection->count > 1) && (now - connection->timestamp) < config->min_idle)
		waitlength = config->min_idle - (now - connection->timestamp);
	else
		waitlength = 0;

	connection->timestamp = now + waitlength;
	count = connection->count;

	if(buf)
		munmap((void *)buf, size);
	close(fd);

	if(waitlength)
		waitfor(config, waitlength, c->remote_ip, debug, r->server, cookieval);

	if(debug) {
		fprintf(debug, "ip %s count %ld\n", c->remote_ip, count);
		fclose(debug);
	}

	return DECLINED;
}

/*
 * Hold the current thread for some time
 *
 * TODO: Hold any further attempts for this client to connect during the waitfor
 *	time
 */
static void
waitfor(spambotConfig *config, int nsec, const char *ip, FILE *debug, const server_rec *s, const char *cookieval)
{
	struct timeval tv;
	struct timezone tz;
	struct timespec timeout;

	if(debug)
		fprintf(debug, "ip %s waiting %u second%s\n", ip,
			nsec, (nsec == 1) ? "" : "s");

	sendwaitemail(config, s, cookieval, ip, nsec);

	/*
	 * We can't sleep in a multi-threaded environment since it
	 * puts other threads to sleep as well
	 */
	/*sleep(nsec);*/
	pthread_mutex_lock(&sleeper_mutex);
	gettimeofday(&tv, &tz);
	timeout.tv_sec = tv.tv_sec + nsec;
	timeout.tv_nsec = tv.tv_usec * 1000;
	pthread_cond_timedwait(&sleeper_cond, &sleeper_mutex, &timeout);
	pthread_mutex_unlock(&sleeper_mutex);
}

static	const	command_rec spambot_cmds[] = {
	{"SpamBot", spambot_on, NULL, OR_OPTIONS, FLAG,
		"Run a spambot stopper on this host"},
	{"SpamBotDatabaseFile", set_db_file, NULL, OR_OPTIONS, TAKE1,
		"Set the database absolute path, without trailing '/'"},
	{"SpamBotDebugFile", set_dbg_file, NULL, OR_OPTIONS, TAKE1,
		"Set the debugging file"},
	{"SpamBotTriggerLevel", set_trigger_level, NULL, OR_OPTIONS, TAKE1,
		"Set the trigger level (default 100)"},
	{"SpamBotTriggerTime", set_trigger_time, NULL, OR_OPTIONS, TAKE1,
		"Set the trigger time in seconds (default 3600)"},
	{"SpamBotReuseTime", set_reuse_time, NULL, OR_OPTIONS, TAKE1,
		"Set the re-use time in seconds (default 600)"},
	{"SpamBotDenyCode", set_deny_code, NULL, OR_OPTIONS, TAKE1,
		"HTTP code to send when denying access (default 403)"},
	{"SpamBotMinIdleTime", set_min_idle, NULL, OR_OPTIONS, TAKE1,
		"Minimum number of seconds between requests (default 0)"},
	{"SpamBotRedirectPath", set_redirect_path, NULL, OR_OPTIONS, TAKE1,
		"Where to send matches"},
	{"SpamBotWhiteList", add_to_whitelist, NULL, OR_OPTIONS, TAKE1,
		"Sites to always allow access"},
	{"SpamBotAddSuffix", add_to_suffix, NULL, OR_OPTIONS, ITERATE,
		"Suffixes of files to track"},
	{"SpamBotUsertrackCookieName", set_cookie_name, NULL, OR_FILEINFO,
		TAKE1, "name of the tracking cookie used in mod_usertrack"},
	{"SpamBotSendEmail", set_sendemail, NULL, OR_OPTIONS, FLAG,
		"Send a message to the administrator when a site is blocked"},
	{ NULL }
};

static	const	handler_rec	spambot_handlers[] = {
	{	"spambot",	spambot	},
	{	"text/html",	spambot	},
	{	NULL,		NULL	},
};

module MODULE_VAR_EXPORT spambot_module = {
	STANDARD_MODULE_STUFF,
	spambot_server_init,	/* initializer */
	create_spambot_dir,	/* create per-dir config */
	merge_spambot_dir,	/* merge per-dir config */
	create_spambot_server,	/* server config */
	NULL,			/* merge server config */
	spambot_cmds,		/* command table */
	spambot_handlers,	/* handlers */
	NULL,			/* filename translation */
	NULL,			/* check_user_id */
	NULL,			/* check auth */
	NULL,			/* check access */
	NULL,			/* type_checker */
	NULL,			/* fixups */
	NULL,			/* logger */
	NULL,			/* header parser */
	NULL,			/* child_init */
	NULL,
	NULL			/* post read-request */
};

/* FIXME: use Apache's built in table */
static const char *
mime(const char *filename)
{
	if(ap_strcasecmp_match(filename, "*.html") == 0)
		return "text/html";
	if(ap_strcasecmp_match(filename, "*.htm") == 0)
		return "text/html";
	if(ap_strcasecmp_match(filename, "*.txt") == 0)
		return "text/plain";
	if(ap_strcasecmp_match(filename, "*.gif") == 0)
		return "image/gif";
	if(ap_strcasecmp_match(filename, "*.jpg") == 0)
		return "image/jpeg";
	if(ap_strcasecmp_match(filename, "*.jpeg") == 0)
		return "image/jpeg";
	if(ap_strcasecmp_match(filename, "*.mpg") == 0)
		return "video/mpeg";
	if(ap_strcasecmp_match(filename, "*.mpeg") == 0)
		return "video/mpeg";
	if(ap_strcasecmp_match(filename, "*.pdf") == 0)
		return "application/pdf";
	return NULL;
}

static void
sendblockedemail(const spambotConfig *config, const server_rec *s, const char *cookieval, const char *name, const char *ip)
{
	const char *remote;
	FILE *sendmail;
	char cmd[128];

	if(!config->sendemail)
		return;

	if(cookieval)
		remote = cookieval;
	else if(name)
		remote = name;
	else if(ip)
		remote = ip;
	else
		return;

	snprintf(cmd, sizeof(cmd) - 1, "%s -t -i", SENDMAIL_BIN);

	sendmail = popen(cmd, "w");

	if(sendmail) {
		fprintf(sendmail, "To: %s\n", s->server_admin);
		fprintf(sendmail, "From: %s\n", s->server_admin);
		fprintf(sendmail, "Subject: WARNING: spambot from %s\n\n",
			remote);

		fputs("This is an automatic message.\n\n", sendmail);

		fputs("Mod_spambot has detected a scan from ", sendmail);

		if(cookieval)
			fprintf(sendmail, "the user %s", cookieval);
		else if(name)
			fprintf(sendmail, "the site %s", name);
		else
			fprintf(sendmail, "the IP address %s", ip);

		fputs(".\n\nMod_spambot has blocked further requests from ",
			sendmail);

		if(config->reuse_time == 1)
			fputs("the client for 1 second.\n", sendmail);
		else
			fprintf(sendmail, "the client for %d seconds.\n",
				config->reuse_time);

		pclose(sendmail);
	}
}

/*
 * TODO: handle connection->emailSent
 */
static void
sendwaitemail(const spambotConfig *config, const server_rec *s, const char *cookieval, const char *ip, int seconds)
{
	const char *remote;
	FILE *sendmail;
	char cmd[128];

	if(!config->sendemail)
		return;

	/* TODO: send username if known */
	if(cookieval)
		remote = cookieval;
	else if(ip)
		remote = ip;
	else
		remote = "remote user";

	snprintf(cmd, sizeof(cmd) - 1, "%s -t -i", SENDMAIL_BIN);

	sendmail = popen(cmd, "w");

	if(sendmail) {
		fprintf(sendmail, "To: %s\n", s->server_admin);
		fprintf(sendmail, "From: %s\n", s->server_admin);
		fprintf(sendmail, "Subject: WARNING: spambot from %s\n\n",
			remote);

		fputs("This is an automatic message.\n\n", sendmail);

		fputs("Mod_spambot has throttled back ", sendmail);

		if(cookieval)
			fprintf(sendmail, "the user %s", cookieval);
		else if(ip)
			fprintf(sendmail, "the IP address %s", ip);

		if(seconds == 1)
			fputs(" for 1 second.\n", sendmail);
		else
			fprintf(sendmail, " for %d seconds.\n", seconds);

		pclose(sendmail);
	}
}
