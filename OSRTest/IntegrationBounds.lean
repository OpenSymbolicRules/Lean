import OSR.IntegrationBounds

open OSR OSR.Calculus

-- RUBI LeQ[-2, m+n, 0] retains its upper endpoint as the final guard.
#guard IntegrationBounds.rubi_4_5_2_1_r39.conditions.getLast? ==
  some (.ge (.int 0) (.app2 .add (.var "m") (.var "n")))

-- A direct positive-integer guard supplies both membership and the comparison.
#guard IntegrationBounds.rubi_4_1_5_r41.independent.contains "m"
#guard IntegrationBounds.rubi_4_1_5_r41.conditions.contains (.int (.var "m"))
#guard IntegrationBounds.rubi_4_1_5_r41.conditions.contains (.gt (.var "m") (.int 0))

-- Only evidence for the complete source guard is exposed in the catalogue.
#guard IntegrationBounds.entries.length == 63
#guard (IntegrationBounds.entries.filter (!·.counterexamples.isEmpty)).length == 10
#guard IntegrationBounds.entries.all fun e => e.proofs.isEmpty
#guard IntegrationBounds.outside.length == 10
#guard IntegrationBounds.replaced.length == 49
