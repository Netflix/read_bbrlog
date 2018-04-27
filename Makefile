PROG=		read_bbrlog
SRCS=		${PROG}.c
WARNS?=		6
DEBUG_FLAGS=	-ggdb
LDADD+=		-lbbparse -llzma

.include <bsd.prog.mk>
