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

# Replay each compiled module in the kernel with leanchecker.  Each replay loads
# Mathlib (about 3 GB of memory), so replays run one at a time unless
# OSR_CHECK_JOBS asks for more in parallel; any failure fails the recipe.
check:
	printf '%s\n' OSR.Registry OSR.LogicOps OSR.Expr OSR.Interp OSR.Rule OSR.Rewrite OSR.Termination OSR.Semantics OSR.OMObject OSR.Catalog OSR.Trigonometry OSR.Algebra OSR.LogicCore OSR.Logic OSR.Decide OSR.Calculus OSR.IntegrationRec OSR.IntegrationRec2 OSR.IntegrationRec3 OSR.IntegrationRec4 OSR.IntegrationRec5 OSR.IntegrationRec6 OSR.IntegrationRec7 OSR.IntegrationRec8 OSR.IntegrationRec9 OSR.IntegrationRec10 OSR.IntegrationRec11 OSR.IntegrationRec12 OSR.IntegrationRec13 OSR.IntegrationRec14 OSR.IntegrationRec15 OSR.IntegrationRec16 OSR.IntegrationRec17 OSR.IntegrationRec18 OSR.IntegrationRec19 OSR.IntegrationRec20 OSR.IntegrationRec21 OSR.IntegrationRec22 OSR.IntegrationRec23 OSR.IntegrationRec24 OSR.IntegrationRec25 OSR.IntegrationRec26 OSR.IntegrationRec27 OSR.IntegrationRec28 OSR.IntegrationRec29 OSR.IntegrationRec30 OSR.IntegrationRec31 OSR.IntegrationRec32 OSR.IntegrationRec33 OSR.IntegrationRec34 OSR.IntegrationRec35 OSR.IntegrationRec36 OSR.IntegrationRec37 OSR.IntegrationRec38 OSR.IntegrationRec39 OSR.IntegrationRec40 OSR.IntegrationRec41 OSR.IntegrationRec42 OSR.IntegrationRec43 OSR.IntegrationRec44 OSR.IntegrationRec45 OSR.IntegrationRec46 OSR.IntegrationRec47 OSR.IntegrationRec48 OSR.IntegrationFindings OSR.IntegrationNum1 OSR.IntegrationRec49 OSR.IntegrationRec50 OSR.IntegrationRec51 OSR.IntegrationRec52 OSR.IntegrationRec53 OSR.IntegrationRec54 OSR.IntegrationRec55 OSR.IntegrationRec56 OSR.IntegrationRec57 OSR.IntegrationRec58 OSR.IntegrationRec59 OSR.IntegrationRec60 OSR.IntegrationRec61 OSR.IntegrationRec62 OSR.IntegrationRec63 OSR.IntegrationRec64 OSR.IntegrationRec65 OSR.IntegrationRec66 OSR.IntegrationRec67 OSR.IntegrationRec68 OSR.IntegrationRec69 OSR.IntegrationRec70 OSR.IntegrationRec71 OSR.IntegrationRec72 OSR.IntegrationRec73 OSR.IntegrationRec74 OSR.IntegrationRec75 OSR.IntegrationRec76 OSR.IntegrationRec77 OSR.IntegrationRec78 OSR.IntegrationRec79 OSR.IntegrationRec80 OSR.IntegrationRec81 OSR.IntegrationRec82 OSR.IntegrationRec83 OSR.IntegrationRec84 OSR.IntegrationRec85 OSR.IntegrationRec86 OSR.IntegrationRec87 OSR.IntegrationRec88 OSR.IntegrationRec89 OSR.IntegrationRec90 OSR.IntegrationRec91 OSR.IntegrationRec92 OSR.IntegrationRec93 OSR.IntegrationRec94 OSR.IntegrationRec95 OSR.IntegrationRec96 OSR.IntegrationRec97 OSR.IntegrationRec98 OSR.IntegrationRec99 OSR.IntegrationRec100 OSR.IntegrationRec101 OSR.IntegrationRec102 OSR.IntegrationRec103 OSR.IntegrationRec104 OSR.IntegrationRec105 OSR.IntegrationRec106 OSR.IntegrationRec107 OSR.IntegrationRec108 OSR.IntegrationRec109 OSR.IntegrationRec110 OSR.IntegrationRec111 OSR.IntegrationRec112 OSR.IntegrationRec113 OSR.IntegrationRec114 OSR.IntegrationRec115 OSR.IntegrationRec116 OSR.IntegrationRec117 OSR.IntegrationRec118 OSR.IntegrationRec119 OSR.IntegrationRec120 OSR.IntegrationRec121 OSR.IntegrationRec122 OSR.IntegrationRec123 OSR.IntegrationRec124 OSR.IntegrationRec125 OSR.IntegrationRec126 OSR.IntegrationRec127 OSR.Integration OSR.Export | xargs -P "${OSR_CHECK_JOBS:-1}" -I{} sh -c 'lake env leanchecker {} || exit 255'

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
