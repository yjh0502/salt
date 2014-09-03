BASE_DIR = $(shell pwd)
SUPPORT_DIR=$(BASE_DIR)/support
ERLC ?= $(shell which erlc)
ESCRIPT ?= $(shell which escript)
ERL ?= $(shell which erl)
APP := salt 
REBAR?= rebar

$(if $(ERLC),,$(warning "Warning: No Erlang found in your path, this will probably not work"))

$(if $(ESCRIPT),,$(warning "Warning: No escript found in your path, this will probably not work"))

.PHONY: doc

all: compile

compile:
	@$(REBAR) compile

doc:
	@$(REBAR) -C doc skip_deps=true

test: compile
	@$(ERL) -pa $(BASE_DIR)/ebin -boot start_sasl -noshell \
		-eval 'salt_test:all().' \
		-eval 'init:stop().'
clean:
	@$(REBAR) clean
	@rm -f doc/*.html doc/*.css doc/edoc-info doc/*.png
