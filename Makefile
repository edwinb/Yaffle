# This is (mostly) the Idris2 Makefile with s/IDRIS2/YAFFLE/ and the
# library building removed. Not all of it makes sense yet; it will be
# reinstated gradually
include config.mk

# Idris 2 executable used to bootstrap
export YAFFLE_BOOT ?= idris2

# Idris 2 executable we're building
NAME = yaffle
TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${NAME}

# Default code generator. This is passed to the libraries for incremental
# builds, but overridable via environment variables or arguments to make
YAFFLE_CG ?= chez

MAJOR=0
MINOR=8
PATCH=0

GIT_SHA1=
ifeq ($(shell git status >/dev/null 2>&1; echo $$?), 0)
	# inside a git repo
	ifneq ($(shell git describe --exact-match --tags >/dev/null 2>&1; echo $$?), 0)
		# not tagged as a released version, so add sha1 of this build in between releases
		GIT_SHA1 := $(shell git rev-parse --short=9 HEAD)
	endif
endif
VERSION_TAG ?= $(GIT_SHA1)

export YAFFLE_VERSION := ${MAJOR}.${MINOR}.${PATCH}
export NAME_VERSION := ${NAME}-${YAFFLE_VERSION}
YAFFLE_SUPPORT := libyaffle_support${SHLIB_SUFFIX}
YAFFLE_APP_IPKG := yaffle.ipkg
YAFFLE_LIB_IPKG := yaffleapi.ipkg

ifeq ($(OS), windows)
	# This produces D:/../.. style paths
	YAFFLE_PREFIX := $(shell cygpath -m ${PREFIX})
	YAFFLE_CURDIR := $(shell cygpath -m ${CURDIR})
	SEP := ;
else
	YAFFLE_PREFIX := ${PREFIX}
	YAFFLE_CURDIR := ${CURDIR}
	SEP := :
endif

TEST_PREFIX ?= ${YAFFLE_CURDIR}/build/env

# Library and data paths for bootstrap-test
YAFFLE_BOOT_PREFIX := ${YAFFLE_CURDIR}/bootstrap-build

# These are the library path in the build dir to be used during build
YAFFLE_LIBRARIES = prelude base linear network contrib test

YAFFLE_BOOT_PATH =
$(foreach library,$(YAFFLE_LIBRARIES),$(eval YAFFLE_BOOT_PATH := $(YAFFLE_BOOT_PATH)$(YAFFLE_CURDIR)/libs/$(library)/build/ttc$(SEP)))
export YAFFLE_BOOT_PATH := "$(YAFFLE_BOOT_PATH)"

export SCHEME

.PHONY: all idris2-exec libdocs testenv testenv-clean support support-clean clean FORCE

all: support ${TARGET} libs

idris2-exec: ${TARGET}

${TARGET}: src/IdrisPaths.idr
	${YAFFLE_BOOT} --build ${YAFFLE_APP_IPKG}

# We use FORCE to always rebuild IdrisPath so that the git SHA1 info is always up to date
src/IdrisPaths.idr: FORCE
	echo "-- @""generated" > src/IdrisPaths.idr
	echo 'module IdrisPaths' >> src/IdrisPaths.idr
	echo 'export idrisVersion : ((Nat,Nat,Nat), String); idrisVersion = ((${MAJOR},${MINOR},${PATCH}), "${VERSION_TAG}")' >> src/IdrisPaths.idr
	echo 'export yprefix : String; yprefix="${YAFFLE_PREFIX}"' >> src/IdrisPaths.idr

FORCE:

prelude:
	${MAKE} -C libs/prelude YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

base: prelude
	${MAKE} -C libs/base YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

network: prelude linear
	${MAKE} -C libs/network YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

contrib: base
	${MAKE} -C libs/contrib YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

test-lib: contrib
	${MAKE} -C libs/test YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

linear: prelude
	${MAKE} -C libs/linear YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

papers: contrib linear
	${MAKE} -C libs/papers YAFFLE=${TARGET} YAFFLE_INC_CGS=${YAFFLE_CG} YAFFLE_PATH=${YAFFLE_BOOT_PATH}

bootstrap-libs : prelude base linear network
#libs : prelude base contrib network test-lib linear papers
# no libs yet!
libs : 

libdocs:
	${MAKE} -C libs/prelude docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}
	${MAKE} -C libs/base docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}
	${MAKE} -C libs/contrib docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}
	${MAKE} -C libs/network docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}
	${MAKE} -C libs/test docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}
	${MAKE} -C libs/linear docs YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH}


ifeq ($(OS), windows)
${TEST_PREFIX}/${NAME_VERSION} :
	${MAKE} install-support PREFIX=${TEST_PREFIX}
	cp -rf ${YAFFLE_CURDIR}/libs/prelude/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/prelude-${YAFFLE_VERSION}
	cp -rf ${YAFFLE_CURDIR}/libs/base/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/base-${YAFFLE_VERSION}
	cp -rf ${YAFFLE_CURDIR}/libs/linear/build/ttc  ${TEST_PREFIX}/${NAME_VERSION}/linear-${YAFFLE_VERSION}
	cp -rf ${YAFFLE_CURDIR}/libs/network/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/network-${YAFFLE_VERSION}
	cp -rf ${YAFFLE_CURDIR}/libs/contrib/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/contrib-${YAFFLE_VERSION}
	cp -rf ${YAFFLE_CURDIR}/libs/test/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/test-${YAFFLE_VERSION}
else
${TEST_PREFIX}/${NAME_VERSION} :
	${MAKE} install-support PREFIX=${TEST_PREFIX}
	ln -sf ${YAFFLE_CURDIR}/libs/prelude/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/prelude-${YAFFLE_VERSION}
	ln -sf ${YAFFLE_CURDIR}/libs/base/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/base-${YAFFLE_VERSION}
	ln -sf ${YAFFLE_CURDIR}/libs/linear/build/ttc  ${TEST_PREFIX}/${NAME_VERSION}/linear-${YAFFLE_VERSION}
	ln -sf ${YAFFLE_CURDIR}/libs/network/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/network-${YAFFLE_VERSION}
	ln -sf ${YAFFLE_CURDIR}/libs/contrib/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/contrib-${YAFFLE_VERSION}
	ln -sf ${YAFFLE_CURDIR}/libs/test/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/test-${YAFFLE_VERSION}
endif

.PHONY: ${TEST_PREFIX}/${NAME_VERSION}

testenv:
	@${MAKE} ${TEST_PREFIX}/${NAME_VERSION}
	@${MAKE} -C tests testbin YAFFLE=${TARGET} YAFFLE_PREFIX=${TEST_PREFIX}

testenv-clean:
	$(RM) -r ${TEST_PREFIX}/${NAME_VERSION}

ci-ubuntu-test: test
ci-macos-test: test
ci-windows-test:
	@${MAKE} test except="idris2/repl005"

test: testenv
	@echo
	@echo "NOTE: \`${MAKE} test\` does not rebuild Idris or the libraries packaged with it; to do that run \`${MAKE}\`"
	@if [ ! -x "${TARGET}" ]; then echo "ERROR: Missing YAFFLE executable. Cannot run tests!\n"; exit 1; fi
	@echo
	@${MAKE} -C tests only=$(only) except=$(except) YAFFLE=${TARGET} YAFFLE_PREFIX=${TEST_PREFIX}


retest: testenv
	@echo
	@echo "NOTE: \`${MAKE} retest\` does not rebuild Idris or the libraries packaged with it; to do that run \`${MAKE}\`"
	@if [ ! -x "${TARGET}" ]; then echo "ERROR: Missing YAFFLE executable. Cannot run tests!\n"; exit 1; fi
	@echo
	@${MAKE} -C tests retest only=$(only) YAFFLE=${TARGET} YAFFLE_PREFIX=${TEST_PREFIX}

test-installed:
	@${MAKE} -C tests testbin      YAFFLE=$(YAFFLE_PREFIX)/bin/idris2 YAFFLE_PREFIX=${YAFFLE_PREFIX}
	@${MAKE} -C tests only=$(only) YAFFLE=$(YAFFLE_PREFIX)/bin/idris2 YAFFLE_PREFIX=${YAFFLE_PREFIX}

support:
	@${MAKE} -C support/c
	@${MAKE} -C support/refc
	@${MAKE} -C support/chez

support-clean:
	@${MAKE} -C support/c cleandep
	@${MAKE} -C support/refc cleandep
	@${MAKE} -C support/chez clean

clean-libs:
	${MAKE} -C libs/prelude clean
	${MAKE} -C libs/base clean
	${MAKE} -C libs/contrib clean
	${MAKE} -C libs/network clean
	${MAKE} -C libs/test clean
	${MAKE} -C libs/linear clean
	${MAKE} -C libs/papers clean

clean: clean-libs support-clean testenv-clean
	-${YAFFLE_BOOT} --clean ${YAFFLE_APP_IPKG}
	$(RM) src/IdrisPaths.idr
	${MAKE} -C tests clean
	$(RM) -r build

install: install-idris2 install-support install-libs
bootstrap-install: install-idris2 install-support install-bootstrap-libs

install-api: src/IdrisPaths.idr
	${YAFFLE_BOOT} --install ${YAFFLE_LIB_IPKG}

install-with-src-api: src/IdrisPaths.idr
	${YAFFLE_BOOT} --install-with-src ${YAFFLE_LIB_IPKG}

install-idris2:
	mkdir -p ${PREFIX}/bin/
	install ${TARGET} ${PREFIX}/bin
ifeq ($(OS), windows)
	-install ${TARGET}.cmd ${PREFIX}/bin
endif
	mkdir -p ${PREFIX}/lib/
	install support/c/${YAFFLE_SUPPORT} ${PREFIX}/lib
	mkdir -p ${PREFIX}/bin/${NAME}_app
	install ${TARGETDIR}/${NAME}_app/* ${PREFIX}/bin/${NAME}_app

install-support:
	mkdir -p ${PREFIX}/${NAME_VERSION}/support/docs
	mkdir -p ${PREFIX}/${NAME_VERSION}/support/racket
	mkdir -p ${PREFIX}/${NAME_VERSION}/support/gambit
	mkdir -p ${PREFIX}/${NAME_VERSION}/support/js
	install -m 644 support/docs/*.css ${PREFIX}/${NAME_VERSION}/support/docs
	install -m 644 support/racket/* ${PREFIX}/${NAME_VERSION}/support/racket
	install -m 644 support/gambit/* ${PREFIX}/${NAME_VERSION}/support/gambit
	install -m 644 support/js/* ${PREFIX}/${NAME_VERSION}/support/js
	@${MAKE} -C support/c install
	@${MAKE} -C support/refc install
	@${MAKE} -C support/chez install

install-bootstrap-libs:
	${MAKE} -C libs/prelude install YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/base install    YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/linear install  YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/network install YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}

install-libs: install-bootstrap-libs
	${MAKE} -C libs/contrib install YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/test install YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}

install-with-src-libs:
	${MAKE} -C libs/prelude install-with-src YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/base install-with-src    YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/contrib install-with-src YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/network install-with-src YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/test install-with-src    YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}
	${MAKE} -C libs/linear install-with-src  YAFFLE=${TARGET} YAFFLE_PATH=${YAFFLE_BOOT_PATH} YAFFLE_INC_CGS=${YAFFLE_CG}

install-libdocs: libdocs
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/prelude
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/base
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/contrib
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/network
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/test
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/linear
	cp -r libs/prelude/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/prelude
	cp -r libs/base/build/docs/*    ${PREFIX}/${NAME_VERSION}/docs/base
	cp -r libs/contrib/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/contrib
	cp -r libs/network/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/network
	cp -r libs/test/build/docs/*    ${PREFIX}/${NAME_VERSION}/docs/test
	cp -r libs/linear/build/docs/*  ${PREFIX}/${NAME_VERSION}/docs/linear
	install -m 644 support/docs/*   ${PREFIX}/${NAME_VERSION}/docs


.PHONY: bootstrap bootstrap-build bootstrap-racket bootstrap-racket-build bootstrap-test bootstrap-clean

# Bootstrapping using SCHEME
bootstrap: support
	@if [ "$$(echo '(threaded?)' | $(SCHEME) --quiet)" = "#f" ] ; then \
		echo "ERROR: Chez is missing threading support" ; exit 1 ; fi
	mkdir -p bootstrap-build/idris2_app
	cp support/c/${YAFFLE_SUPPORT} bootstrap-build/idris2_app/
	sed 's/libidris2_support.so/${YAFFLE_SUPPORT}/g; s|__PREFIX__|${YAFFLE_BOOT_PREFIX}|g' \
		bootstrap/idris2_app/idris2.ss \
		> bootstrap-build/idris2_app/idris2-boot.ss
	$(SHELL) ./bootstrap-stage1-chez.sh
	YAFFLE_CG="chez" $(SHELL) ./bootstrap-stage2.sh

# Bootstrapping using racket
bootstrap-racket: support
	mkdir -p bootstrap-build/idris2_app
	cp support/c/${YAFFLE_SUPPORT} bootstrap-build/idris2_app/
	sed 's|__PREFIX__|${YAFFLE_BOOT_PREFIX}|g' \
		bootstrap/idris2_app/idris2.rkt \
		> bootstrap-build/idris2_app/idris2-boot.rkt
	$(SHELL) ./bootstrap-stage1-racket.sh
	YAFFLE_CG="racket" $(SHELL) ./bootstrap-stage2.sh

bootstrap-test:
	$(MAKE) test INTERACTIVE='' YAFFLE_PREFIX=${YAFFLE_BOOT_PREFIX}

ci-windows-bootstrap-test:
	$(MAKE) test except="idris2/repl005" INTERACTIVE='' YAFFLE_PREFIX=${YAFFLE_BOOT_PREFIX}

bootstrap-clean:
	$(RM) -r bootstrap-build


.PHONY: distclean

distclean: clean bootstrap-clean
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
