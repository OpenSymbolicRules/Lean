# Entry points for the Lean-native OSR core.

export PATH := env_var('HOME') + "/.elan/bin:" + env_var('PATH')

# Fetch pinned dependencies and the prebuilt Mathlib cache.
setup:
	lake exe cache get

# Compile the registry, the rules and their proofs (kernel-checked).
build:
	lake build

# Run the test library (#guard checks and examples).
test:
	lake build OSRTest

# Build the documentation and LLM text exports under docs/build/.
doc:
	julia --project=docs -e 'using Pkg; Pkg.instantiate(); include("docs/make.jl")'

# Replay each compiled module in the kernel with leanchecker.  Modules are
# replayed one at a time: each replay loads Mathlib (about 3 GB of memory).
check:
	for m in OSR.Registry OSR.LogicOps OSR.Expr OSR.Interp OSR.Rule OSR.Rewrite OSR.Termination OSR.Semantics OSR.OMObject OSR.Catalog OSR.Trigonometry OSR.Algebra OSR.LogicCore OSR.Logic OSR.Decide OSR.Calculus OSR.IntegrationRec OSR.IntegrationRec2 OSR.IntegrationRec3 OSR.Integration OSR.Export; do lake env leanchecker $m || exit 1; done

# Audit proofs and export the interchange JSON to `out`.
export out="generated":
	OSR_OUT_DIR={{out}} OSR_SOURCE_DIGEST=$(scripts/source-digest.sh) lake env lean scripts/Export.lean

# Export twice and require byte-identical output.
determinism:
	rm -rf /tmp/osr-a /tmp/osr-b
	just export /tmp/osr-a
	just export /tmp/osr-b
	diff -r /tmp/osr-a /tmp/osr-b

# Validate the generated JSON against the interchange schema.
validate out="generated":
	check-jsonschema --schemafile schemas/ruleset.schema.json {{out}}/trigonometry.osr.json {{out}}/algebra.osr.json {{out}}/logic.osr.json {{out}}/calculus.osr.json {{out}}/integration.osr.json

# Everything CI runs.
ci: build test check export determinism validate
