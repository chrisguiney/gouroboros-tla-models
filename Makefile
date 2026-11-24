.DEFAULT_GOAL := help
SHELL := bash

# Every model is a .cfg file under specs/. A config whose name ends in Bug.cfg
# is an intentionally broken teaching example and is expected to FAIL.
CONFIGS := $(filter-out %Bug.cfg,$(wildcard specs/*/*.cfg))

KEEPALIVE := cd specs/01-keepalive && ../../bin/tlc

.PHONY: help install hello hello-bug keepalive keepalive-table keepalive-bugs keepalive-lifecycle connection engine engine-deep chainsync chainsync-deep check clean

help: ## Show this list
	@grep -E '^[a-z-]+:.*## ' $(MAKEFILE_LIST) | awk -F':.*## ' '{printf "  make %-16s %s\n", $$1, $$2}'

install: ## Download Java + TLA+ tools into .tools/ (no sudo)
	@scripts/install-tla.sh

hello: ## Check the hello-world model (proves the install works)
	cd specs/00-hello && ../../bin/tlc -config Hello.cfg Hello.tla

hello-bug: ## Watch TLC catch a bug and print the steps that cause it
	cd specs/00-hello && ../../bin/tlc -config HelloBug.cfg Hello.tla || true

keepalive: ## Check the keep-alive model with honest, slow, and rogue peers
	$(KEEPALIVE) -config KeepAlive.cfg KeepAlive.tla
	$(KEEPALIVE) -config KeepAliveSlow.cfg KeepAlive.tla
	$(KEEPALIVE) -config KeepAliveRogue.cfg KeepAlive.tla

keepalive-table: ## Print the keep-alive receive rule that the Go tests mirror
	@$(KEEPALIVE) -config KeepAliveTable.cfg KeepAliveTable.tla | grep '^<<'

keepalive-bugs: ## Show the keep-alive counterexamples, including the gOuroboros bug (expected to fail)
	$(KEEPALIVE) -config KeepAliveGouroborosBug.cfg KeepAlive.tla || true
	$(KEEPALIVE) -config KeepAliveRogueBug.cfg KeepAlive.tla || true
	$(KEEPALIVE) -config KeepAliveNoTimeoutBug.cfg KeepAlive.tla || true

keepalive-lifecycle: ## Check the gOuroboros server restart against Stop and connection close
	$(KEEPALIVE) -config KeepAliveLifecycle.cfg KeepAliveLifecycle.tla
	$(KEEPALIVE) -config KeepAliveLifecycleClose.cfg KeepAliveLifecycle.tla
	$(KEEPALIVE) -config KeepAliveLifecycleStopBug.cfg KeepAliveLifecycle.tla || true
	$(KEEPALIVE) -config KeepAliveLifecycleSlotBug.cfg KeepAliveLifecycle.tla || true
	$(KEEPALIVE) -config KeepAliveLifecycleCloseBug.cfg KeepAliveLifecycle.tla || true

CONNECTION := cd specs/02-connection && ../../bin/tlc

connection: ## Check the connection: restarts, stop, shared ingress, shutdown
	$(CONNECTION) -config MuxHandover.cfg MuxHandover.tla
	$(CONNECTION) -config MuxHandoverNoCarryBug.cfg MuxHandover.tla || true
	$(CONNECTION) -config MuxHandoverAdmitAllBug.cfg MuxHandover.tla || true
	$(CONNECTION) -config MuxHandoverNoResumeBug.cfg MuxHandover.tla || true
	$(CONNECTION) -config MuxHandoverServerStop.cfg MuxHandover.tla
	$(CONNECTION) -config MuxHandoverClose.cfg MuxHandover.tla
	$(CONNECTION) -config MuxHandoverCloseWindowBug.cfg MuxHandover.tla || true
	$(CONNECTION) -config MuxIngress.cfg MuxIngress.tla
	$(CONNECTION) -config MuxIngressUnsizedBug.cfg MuxIngress.tla || true
	$(CONNECTION) -config MuxIngressBackpressure.cfg MuxIngress.tla
	$(CONNECTION) -config MuxIngressBackpressureDependencyBug.cfg MuxIngress.tla || true
	$(CONNECTION) -config MuxIngressSharedBudget.cfg MuxIngress.tla
	$(CONNECTION) -config MuxIngressSharedBudgetBug.cfg MuxIngress.tla || true
	$(CONNECTION) -config ConnectionShutdown.cfg ConnectionShutdown.tla
	$(CONNECTION) -config ConnectionShutdownLateErrorBug.cfg ConnectionShutdown.tla || true

ENGINE := cd specs/03-engine && ../../bin/tlc

engine: ## Check the protocol engine: admission and pipelining
	$(ENGINE) -config EngineAdmissionKeepAlive.cfg EngineAdmission.tla
	$(ENGINE) -config EngineAdmissionChainSync.cfg EngineAdmission.tla
	$(ENGINE) -config EngineAdmissionBlockFetch.cfg EngineAdmission.tla
	$(ENGINE) -config EngineAdmissionNoContinueBug.cfg EngineAdmission.tla || true
	$(ENGINE) -config EngineAdmissionNoReserveBug.cfg EngineAdmission.tla || true
	$(ENGINE) -config EnginePipeliningBlockFetch.cfg EnginePipelining.tla
	$(ENGINE) -config EnginePipeliningChainSync.cfg EnginePipelining.tla
	$(ENGINE) -config EnginePipeliningNoReservationBug.cfg EnginePipelining.tla || true

engine-deep: ## Check pipelining with two requests in flight (a few minutes)
	$(ENGINE) -workers auto -config EnginePipeliningBlockFetchDeep.cfg EnginePipelining.tla
	$(ENGINE) -workers auto -config EnginePipeliningChainSyncDeep.cfg EnginePipelining.tla

CHAINSYNC := cd specs/04-chainsync && ../../bin/tlc

chainsync: ## Check the chain-sync client: window, Reintersect, stop and restart, queries
	$(CHAINSYNC) -config ChainSyncClient.cfg ChainSyncClient.tla
	$(CHAINSYNC) -config ChainSyncClientStop.cfg ChainSyncClient.tla
	$(CHAINSYNC) -config ChainSyncClientTopUpBug.cfg ChainSyncClient.tla || true
	$(CHAINSYNC) -config ChainSyncClientNoDrainBug.cfg ChainSyncClient.tla || true
	$(CHAINSYNC) -config ChainSyncClientNoDiscardBug.cfg ChainSyncClient.tla || true
	$(CHAINSYNC) -config ChainSyncLifecycleDrain.cfg ChainSyncLifecycle.tla
	$(CHAINSYNC) -config ChainSyncLifecycleRefuse.cfg ChainSyncLifecycle.tla
	$(CHAINSYNC) -config ChainSyncLifecycleClose.cfg ChainSyncLifecycle.tla
	$(CHAINSYNC) -config ChainSyncLifecycleStopBug.cfg ChainSyncLifecycle.tla || true
	$(CHAINSYNC) -config ChainSyncLifecycleCloseOnlyBug.cfg ChainSyncLifecycle.tla || true
	$(CHAINSYNC) -config ChainSyncQueriesPopFirst.cfg ChainSyncQueries.tla
	$(CHAINSYNC) -config ChainSyncQueriesWaitOwn.cfg ChainSyncQueries.tla
	$(CHAINSYNC) -config ChainSyncQueriesBug.cfg ChainSyncQueries.tla || true
	$(CHAINSYNC) -config ChainSyncQueriesNoSyncBug.cfg ChainSyncQueries.tla || true
	$(CHAINSYNC) -config ChainSyncQueriesPopFirstBug.cfg ChainSyncQueries.tla || true

chainsync-deep: ## Check the chain-sync client with a window of three
	$(CHAINSYNC) -workers auto -config ChainSyncClientDeep.cfg ChainSyncClient.tla

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
