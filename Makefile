.DEFAULT_GOAL := help
SHELL := bash

# Every model is a .cfg file under specs/. A config whose name ends in Bug.cfg
# is an intentionally broken teaching example and is expected to FAIL.
CONFIGS := $(filter-out %Bug.cfg,$(wildcard specs/*/*.cfg))

KEEPALIVE := cd specs/01-keepalive && ../../bin/tlc

.PHONY: help install hello hello-bug keepalive keepalive-table keepalive-bugs check clean

help: ## Show this list
	@grep -E '^[a-z-]+:.*## ' $(MAKEFILE_LIST) | awk -F':.*## ' '{printf "  make %-16s %s\n", $$1, $$2}'

install: ## Download Java + TLA+ tools into .tools/ (no sudo)
	@scripts/install-tla.sh

hello: ## Check the hello-world model (proves the install works)
	cd specs/00-hello && ../../bin/tlc -config Hello.cfg Hello.tla

hello-bug: ## Watch TLC catch a bug and print the steps that cause it
	cd specs/00-hello && ../../bin/tlc -config HelloBug.cfg Hello.tla || true

keepalive: ## Check the keep-alive model, with honest and with rogue peers
	$(KEEPALIVE) -config KeepAlive.cfg KeepAlive.tla
	$(KEEPALIVE) -config KeepAliveRogue.cfg KeepAlive.tla

keepalive-table: ## Print the keep-alive receive rule that the Go tests mirror
	@$(KEEPALIVE) -config KeepAliveTable.cfg KeepAliveTable.tla | grep '^<<'

keepalive-bugs: ## Show the two keep-alive counterexamples (expected to fail)
	$(KEEPALIVE) -config KeepAliveRogueBug.cfg KeepAlive.tla || true
	$(KEEPALIVE) -config KeepAliveNoTimeoutBug.cfg KeepAlive.tla || true

check: ## Check every model that is expected to pass
	@set -e; for cfg in $(CONFIGS); do \
	  dir=$$(dirname $$cfg); name=$$(basename $$cfg .cfg); \
	  tla=$$(sed -n 's/^\\\* *SPEC: *//p' $$cfg); tla=$${tla:-$$name.tla}; \
	  echo "==> $$cfg"; \
	  (cd $$dir && ../../bin/tlc -config $$name.cfg $$tla); \
	done

clean: ## Delete TLC scratch output (keeps the installed tools)
	find specs -type d -name states -prune -exec rm -rf {} +
	find specs -name '*_TTrace_*' -delete
