# Shortcuts for building the library and the blueprint. `make` lists the targets.

PORT ?= 8000

.DEFAULT_GOAL := help
.PHONY: help cache build check mk_all blueprint web pdf serve frontier status sorries lines clean-blueprint

help: ## List the targets
	@grep -E '^[a-z_-]+:.*## ' $(MAKEFILE_LIST) | awk -F ':.*## ' '{printf "  %-16s %s\n", $$1, $$2}'

cache: ## Download Mathlib's compiled files
	lake exe cache get

build: ## Build the library
	lake build

check: ## What CI checks: build with warnings as errors, root import file up to date
	lake build --wfail
	lake exe mk_all --check

mk_all: ## Regenerate Coarse.lean and CoarseBlueprint.lean
	lake exe mk_all

# The stamp records when the blueprint was extracted, for `make frontier`.
blueprint: ## Build the tags and extract the blueprint to .lake/build/blueprint
	lake build CoarseBlueprint:blueprint
	touch .lake/build/blueprint/stamp

web: blueprint ## Render the blueprint web page to blueprint/web
	leanblueprint web
	python3 scripts/blueprint_links.py

pdf: blueprint ## Render the blueprint pdf to blueprint/print/print.pdf
	leanblueprint pdf

serve: web ## Render and serve the web blueprint at http://localhost:8000 (PORT=… to change)
	python3 -m http.server $(PORT) --directory blueprint/web

frontier: ## List the frontier, nodes awaiting review, sorried and blocked nodes (no build)
	python3 scripts/blueprint_frontier.py

status: blueprint ## List the state of every blueprint node
	python3 scripts/blueprint_frontier.py --all

sorries: ## List every sorry in the library
	@grep -rn --include='*.lean' -w sorry Coarse || echo "No sorry."

lines: ## List lines over 100 characters in Coarse/ and CoarseBlueprint/ (no build)
	@python3 -c "import glob,sys; bad=[f'{f}:{i}: {len(l)} characters' for f in sorted(glob.glob('Coarse*/**/*.lean',recursive=True)) for i,l in enumerate(open(f,encoding='utf-8').read().split(chr(10)),1) if len(l)>100]; print(chr(10).join(bad) or 'No line over 100 characters.'); sys.exit(1 if bad else 0)"

clean-blueprint: ## Remove the rendered blueprint
	rm -rf blueprint/web blueprint/print blueprint/lean_decls
