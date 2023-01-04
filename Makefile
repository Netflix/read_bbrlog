# ----------------------------------Purpose of this file-----------------------------------

# The following lines of code represents a makefile for building a program called read_bbrlog. It specifies a number of variables that will 
# be used when building the program, such as the name of the program (PROG), the source files that should be compiled to create the program 
# (SRCS), and various flags that should be passed to the compiler (WARNS, DEBUG_FLAGS, CFLAGS, and LDFLAGS).

# The LDADD variable specifies libraries that should be linked with the program, and the .include directive at the end causes the build process 
# to include the contents of the file bsd.prog.mk, which is likely to contain additional build instructions and rules.

# Overall, the purpose of this Makefile is to provide a set of instructions for building the read_bbrlog program using the Make build system. 
# When you run the make command using this Makefile, it will use the specified variables and rules to build the program.

# ----------------------------------End of Purpose of this file-----------------------------------

PROG=		read_bbrlog
SRCS=		${PROG}.c
WARNS?=		6
DEBUG_FLAGS=	-ggdb
LDADD+=		-lbbparse -llzma
CFLAGS+=	-I/usr/local/include
LDFLAGS+=	-L/usr/local/lib

.include <bsd.prog.mk>
