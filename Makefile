OPAM=opam
EXEC=${OPAM} exec
DUNE=${EXEC} dune --

.PHONY: all build clean test top

all: build

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

doc:
	@${DUNE} build @doc

test:
	@$(foreach file, $(wildcard test/*.tt), echo Test $(file) && ./_build/install/default/bin/mitten $(file) 1> /dev/null && echo;)
