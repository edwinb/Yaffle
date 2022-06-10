NAME = yaffle
TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${NAME}

.PHONY: test testenv

testenv:
	make -C tests testbin

test: testenv
	make -C tests YAFFLE=${TARGET}
