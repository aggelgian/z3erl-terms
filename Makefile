.PHONY: clean

TOP  = $(PWD)
ERLC = erlc

WARNS = +warn_exported_vars +warn_unused_import #+warn_missing_spec #+warn_untyped_record
ERLC_FLAGS = +debug_info $(WARNS)

SRC_MODULES = \
	z3erl \
	smt \
	smt_lexer \
	smt_parser

default: $(SRC_MODULES:%=%.beam)

smt_lexer.erl: smt_lexer.xrl
	erl -noshell -eval "leex:file(smt_lexer)" -s init stop

smt_parser.erl: smt_parser.yrl
	erl -noshell -eval "yecc:file(smt_parser)" -s init stop

%.beam: %.erl
	$(ERLC) $(ERLC_FLAGS) $<

clean:
	rm -f *.beam smt_lexer.erl smt_parser.erl
