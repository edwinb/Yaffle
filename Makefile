NAME = yaffle
TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${NAME}

.PHONY: test

test:
	make -C tests YAFFLE=${TARGET}
