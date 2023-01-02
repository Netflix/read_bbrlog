PROG=		read_bbrlog
SRCS=		${PROG}.c
WARNS?=		6
DEBUG_FLAGS=	-ggdb
LDADD+=		-lbbparse -llzma
CFLAGS+=	-I/usr/local/include
LDFLAGS+=	-L/usr/local/lib

.include <bsd.prog.mk>
