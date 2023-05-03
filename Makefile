PROG=		read_bbrlog
SRCS=		${PROG}.c
WARNS?=		6
DEBUG_FLAGS=	-ggdb
LDADD+=		-lbbparse -llzma
CFLAGS+=	-I/usr/local/include
LDFLAGS+=	-L/usr/local/lib
WITHOUT_PIE=true

.include <bsd.prog.mk>
