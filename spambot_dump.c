/*
 *  Copyright (C) 2010 Nigel Horne <njh@bandsman.co.uk>
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
 */
#include <stdio.h>
#include <fcntl.h>
#include <sys/param.h>	/* For MAXHOSTNAMELEN */
#include <arpa/inet.h>
#include <unistd.h>
#include <errno.h>
#include <netdb.h>	/* for gethostbyaddr() */
#include <time.h>

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

union ip_addr {
	in_addr_t	i;
	unsigned	char c[4];
};

int
main(int argc, const char **argv)
{
	int fd;
	connection c;
	time_t now;

	if(argc != 2) {
		fputs("Arg Count\n", stderr);
		return 1;
	}

	fd = open(argv[1], O_RDONLY);
	if(fd < 0) {
		perror(argv[1]);
		return errno;
	}

	printf("%-20.20s ", "HOST");
	printf("%7s", "COUNT");
	printf("%11s\n", "IDLE(secs)");

	time(&now);

	while(read(fd, &c, sizeof(connection)) == sizeof(connection)) {
		const struct hostent *h;
		struct in_addr in_addr;

		if(c.ipaddr == -1)
			continue;
		/* FIXME: continue if this host isn't currently blocked */
		in_addr.s_addr = c.ipaddr;
		h = gethostbyaddr(&in_addr, sizeof(in_addr), AF_INET);
		if(h)
			printf("%-20.20s", h->h_name);
		else {
			const char *buf;
			buf = inet_ntoa(in_addr);
			if(buf)
				printf("%-20.20s", buf);
			else
				continue;
		}
		printf(" %7lu", c.count);
		printf(" %10lu\n", (unsigned long)(now - c.timestamp));
	}
	return close(fd);
}
