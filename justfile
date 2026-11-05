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

# Replay each compiled module in the kernel with leanchecker.  Modules are
# replayed one at a time: each replay loads Mathlib (about 3 GB of memory).
check:
	for m in OSR.Registry OSR.Expr OSR.Interp OSR.Rule OSR.Rewrite OSR.Semantics OSR.Catalog OSR.Trigonometry OSR.Export; do lake env leanchecker $m || exit 1; done

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
	check-jsonschema --schemafile schemas/ruleset.schema.json {{out}}/trigonometry.osr.json

# Everything CI runs.
ci: build test check export determinism validate
