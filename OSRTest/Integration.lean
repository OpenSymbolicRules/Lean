import OSR

/-!
# Integration tests
-/

namespace OSRTest.Integration

open OSR OSR.Calculus OSR.Integration

-- The arctangent candidate is published as a real counterexample, with no
-- unsupported claim about the complex domain.
#guard match Integration.catalog.find? (·.rule.id == "integration.rubi_5_3_7_r19") with
  | none => false
  | some e => e.counterexamples.any (fun p => p.1 == Domain.real) &&
      e.proofs.isEmpty && e.unproved.contains Domain.complex

-- The arcosh rule retains the RUBI conditions and is proved over the reals.
#guard match Integration.catalog.find? (·.rule.id == "integration.rubi_1_1_1_2_r21") with
  | none => false
  | some e => e.proofs.any (fun p => p.1 == Domain.real) &&
      e.counterexamples.isEmpty && e.unproved.contains Domain.complex

-- The analogous arctanh rule is refuted over the reals.
#guard match Integration.catalog.find? (·.rule.id == "integration.rubi_7_3_7_r19") with
  | none => false
  | some e => e.counterexamples.any (fun p => p.1 == Domain.real) &&
      e.proofs.isEmpty && e.unproved.contains Domain.complex

-- The nested exponential rule has an original-condition real counterexample.
#guard match Integration.catalog.find? (·.rule.id == "integration.rubi_2_3_r1") with
  | none => false
  | some e => e.counterexamples.any (fun p => p.1 == Domain.real) &&
      e.proofs.isEmpty && e.unproved.contains Domain.complex

private def t : Expr := .var "t"

-- The twenty rules of the syntactic inventory (FreeQ or NeQ conditions,
-- registered heads, no Int in the result) are migrated or reported, plus
-- 110 rules with residual integrals and seven unmigrated ones.
#guard Integration.catalogVerified.length + Integration.notMigrated.length == 2940
#guard Integration.notMigrated.length == 529
-- A RUBI rule is catalogued once; independently identified strengthened and
-- generalized variants may share the source rule's legacy id.
#guard
  let ls := (Integration.catalogVerified.filter fun e =>
      !e.findings.any (·.startsWith "strengthened:") &&
      !e.findings.any (·.startsWith "generalized:")).filterMap (·.rule.legacyId)
  ls.eraseDups.length == ls.length
#guard (Integration.catalogVerified.filter (·.rule.shape == .antiderivRec)).length == 1887
#guard (Integration.catalogVerified.filter (!·.rule.conditions.isEmpty)).length == 2242
-- RUBI rules with EqQ conditions are stated with relation1#eq (Cond.eq).
#guard (Integration.catalogVerified.filter fun e =>
    e.rule.conditions.any fun | .eq _ _ => true | _ => false).length == 1140

-- RUBI 4.16.1: the new degenerate-coefficient cases are refuted in both
-- domains, with no proof or unresolved domain accidentally attached.
private def degenerateCoefficientIds : List String := [
  "integration.rubi_1_2_2_4_r57", "integration.rubi_1_2_2_4_r58",
  "integration.rubi_2_1_r10", "integration.rubi_4_1_12_r45",
  "integration.rubi_4_1_12_r46", "integration.rubi_4_1_12_r53",
  "integration.rubi_4_1_12_r54", "integration.rubi_3_1_4_r11",
  "integration.rubi_4_7_8_r47", "integration.rubi_4_7_8_r48"]

#guard degenerateCoefficientIds.all fun id =>
  match Integration.catalog.find? (·.rule.id == id) with
  | none => false
  | some e => e.proofs.isEmpty && e.unproved.isEmpty &&
      [Domain.real, Domain.complex].all fun d =>
        (e.counterexamples.lookup d).isSome

-- Strengthened variants: a `_nondegenerate` rule shares the legacy identifier
-- of a refuted catalogue rule, keeps its conditions as a prefix, appends at
-- least one, declares it in a `strengthened:` finding and is proved in both
-- domains.
private def strengthenedIds : List String := [
  "integration.rubi_1_2_1_3_r34_nondegenerate", "integration.rubi_4_1_6_r24_nondegenerate", "integration.rubi_4_1_6_r25_nondegenerate", "integration.rubi_4_1_6_r26_nondegenerate", "integration.rubi_4_1_0_1_r1_nondegenerate", "integration.rubi_4_1_2_2_r34_nondegenerate", "integration.rubi_4_1_2_2_r39_nondegenerate", "integration.rubi_1_2_1_3_r27_nondegenerate", "integration.rubi_1_2_1_3_r59_nondegenerate", "integration.rubi_1_2_1_3_r6_nondegenerate",
  "integration.rubi_4_1_10_r2_nondegenerate", "integration.rubi_4_1_2_2_r26_nondegenerate", "integration.rubi_4_1_4_2_r5_nondegenerate", "integration.rubi_4_1_4_2_r6_nondegenerate", "integration.rubi_4_1_3_1_r23_nondegenerate", "integration.rubi_4_1_5_r6_nondegenerate", "integration.rubi_4_1_6_r14_nondegenerate", "integration.rubi_4_1_6_r27_nondegenerate", "integration.rubi_4_1_6_r28_nondegenerate", "integration.rubi_4_1_6_r29_nondegenerate", "integration.rubi_4_1_6_r41_nondegenerate", "integration.rubi_4_1_6_r42_nondegenerate", "integration.rubi_4_1_6_r43_nondegenerate", "integration.rubi_4_1_1_2_r3_x_nondegenerate", "integration.rubi_4_1_7_r14_nondegenerate", "integration.rubi_4_1_7_r5_nondegenerate", "integration.rubi_4_1_6_r30_nondegenerate",
  "integration.rubi_4_1_4_1_r3_nondegenerate", "integration.rubi_4_1_4_1_r5_nondegenerate", "integration.rubi_4_1_4_1_r12_nondegenerate", "integration.rubi_4_1_4_1_r13_nondegenerate", "integration.rubi_4_1_4_1_r14_nondegenerate", "integration.rubi_4_1_4_1_r15_nondegenerate", "integration.rubi_4_1_4_1_r10_nondegenerate", "integration.rubi_4_1_4_1_r11_nondegenerate", "integration.rubi_4_1_4_2_r3_nondegenerate", "integration.rubi_4_1_4_2_r4_nondegenerate", "integration.rubi_4_3_2_1_r7_nondegenerate", "integration.rubi_4_3_2_1_r8_nondegenerate", "integration.rubi_4_3_2_1_r20_nondegenerate", "integration.rubi_4_3_2_1_r21_nondegenerate", "integration.rubi_4_3_3_1_r4_nondegenerate", "integration.rubi_4_3_3_1_r5_nondegenerate", "integration.rubi_4_3_4_1_r12_nondegenerate", "integration.rubi_4_3_4_1_r13_nondegenerate", "integration.rubi_4_3_4_1_r14_nondegenerate", "integration.rubi_4_3_4_1_r15_nondegenerate", "integration.rubi_4_3_4_2_r4_nondegenerate", "integration.rubi_4_3_4_2_r6_nondegenerate", "integration.rubi_4_3_4_2_r7_nondegenerate", "integration.rubi_4_3_1_1_r10_nondegenerate",
  "integration.rubi_4_1_2_1_r17_nondegenerate", "integration.rubi_4_1_2_1_r25_nondegenerate", "integration.rubi_4_1_2_1_r27_nondegenerate",
  "integration.rubi_4_1_2_1_r26_nondegenerate", "integration.rubi_4_1_2_1_r28_nondegenerate", "integration.rubi_4_1_2_1_r57_nondegenerate", "integration.rubi_4_1_2_1_r58_nondegenerate",
  "integration.rubi_4_1_3_1_r21_nondegenerate", "integration.rubi_4_1_3_1_r37_nondegenerate", "integration.rubi_4_1_4_2_r36_nondegenerate", "integration.rubi_4_1_4_2_r35_nondegenerate", "integration.rubi_4_1_2_1_r89_nondegenerate", "integration.rubi_1_1_3_5_r31_nondegenerate", "integration.rubi_1_2_1_2_r2_nondegenerate", "integration.rubi_1_2_1_3_r21_nondegenerate", "integration.rubi_1_2_1_4_r4_nondegenerate", "integration.rubi_1_2_1_3_r37_nondegenerate", "integration.rubi_1_2_3_4_r18_nondegenerate", "integration.rubi_1_2_3_3_r51_nondegenerate", "integration.rubi_1_2_3_3_r11_nondegenerate", "integration.rubi_4_1_2_2_r78_nondegenerate", "integration.rubi_4_1_2_2_r48_nondegenerate", "integration.rubi_4_1_5_r37_nondegenerate", "integration.rubi_4_1_5_r38_nondegenerate",
  "integration.rubi_4_1_4_2_r2_nondegenerate", "integration.rubi_4_1_4_2_r1_nondegenerate", "integration.rubi_4_3_4_2_r2_nondegenerate", "integration.rubi_4_3_4_2_r1_nondegenerate",
  "integration.rubi_4_3_3_1_r19_nondegenerate", "integration.rubi_4_3_10_r17_nondegenerate",
  "integration.rubi_6_7_9_r9_nondegenerate", "integration.rubi_6_7_9_r10_nondegenerate", "integration.rubi_6_7_9_r4_nondegenerate", "integration.rubi_4_3_2_1_r4_nondegenerate", "integration.rubi_4_1_2_1_r2_nondegenerate", "integration.rubi_4_3_3_1_r2_nondegenerate", "integration.rubi_4_3_2_1_r19_nondegenerate", "integration.rubi_4_1_2_1_r13_nondegenerate", "integration.rubi_6_1_13_r9_nondegenerate", "integration.rubi_6_1_13_r10_nondegenerate", "integration.rubi_4_7_9_r76_nondegenerate", "integration.rubi_4_7_9_r77_nondegenerate", "integration.rubi_6_7_9_r78_nondegenerate", "integration.rubi_6_7_9_r79_nondegenerate",
  "integration.rubi_4_7_9_r28_nondegenerate", "integration.rubi_4_7_9_r29_nondegenerate", "integration.rubi_6_7_9_r23_nondegenerate", "integration.rubi_6_7_9_r24_nondegenerate", "integration.rubi_6_7_9_r25_nondegenerate", "integration.rubi_6_7_9_r30_nondegenerate",
  "integration.rubi_1_1_1_4_r16_nondegenerate", "integration.rubi_1_1_3_5_r27_nondegenerate",
  "integration.rubi_6_7_9_r1_nondegenerate", "integration.rubi_6_7_9_r2_nondegenerate", "integration.rubi_4_7_9_r15_nondegenerate", "integration.rubi_6_7_9_r14_nondegenerate",
  "integration.rubi_4_1_2_2_r47_nondegenerate", "integration.rubi_4_1_2_2_r83_nondegenerate",
  "integration.rubi_4_1_4_1_r6_nondegenerate", "integration.rubi_4_3_4_1_r3_nondegenerate", "integration.rubi_4_1_2_2_r35_nondegenerate", "integration.rubi_4_1_5_r32_nondegenerate", "integration.rubi_4_1_5_r31_nondegenerate", "integration.rubi_4_1_10_r8_nondegenerate",
  "integration.rubi_4_7_4_r6_nondegenerate", "integration.rubi_4_7_4_r7_nondegenerate", "integration.rubi_4_7_4_r31_nondegenerate",
  "integration.rubi_4_1_2_1_r23_nondegenerate",
  "integration.rubi_4_1_9_r29_nondegenerate", "integration.rubi_4_1_9_r30_nondegenerate", "integration.rubi_4_3_9_r19_nondegenerate", "integration.rubi_4_3_9_r20_nondegenerate", "integration.rubi_4_1_9_r5_nondegenerate", "integration.rubi_4_1_9_r6_nondegenerate", "integration.rubi_4_3_9_r9_nondegenerate", "integration.rubi_4_3_9_r10_nondegenerate", "integration.rubi_4_3_9_r15_nondegenerate", "integration.rubi_4_3_9_r16_nondegenerate",
  "integration.rubi_4_1_2_2_r6_nondegenerate",
  "integration.rubi_4_1_9_r1_nondegenerate", "integration.rubi_4_1_9_r2_nondegenerate", "integration.rubi_4_3_9_r1_nondegenerate", "integration.rubi_4_3_9_r2_nondegenerate",
  "integration.rubi_5_3_1_r5_nondegenerate", "integration.rubi_5_3_2_r13_nondegenerate", "integration.rubi_4_1_2_1_r56_nondegenerate", "integration.rubi_4_1_4_1_r7_nondegenerate", "integration.rubi_4_3_4_1_r4_nondegenerate",
  "integration.rubi_4_1_10_r1_nondegenerate", "integration.rubi_4_1_7_r3_nondegenerate", "integration.rubi_4_3_1_1_r1_nondegenerate", "integration.rubi_4_7_9_r47_nondegenerate", "integration.rubi_4_7_9_r48_nondegenerate",
  "integration.rubi_4_1_2_1_r15_nondegenerate", "integration.rubi_4_1_4_1_r1_nondegenerate", "integration.rubi_4_3_1_1_r5_nondegenerate", "integration.rubi_4_3_4_1_r1_nondegenerate", "integration.rubi_4_3_4_1_r2_nondegenerate",
  "integration.rubi_4_1_4_1_r2_nondegenerate",
  "integration.rubi_4_1_1_1_r6_nondegenerate", "integration.rubi_4_1_1_1_r2_nondegenerate", "integration.rubi_6_1_13_r7_nondegenerate", "integration.rubi_6_1_13_r8_nondegenerate", "integration.rubi_4_3_2_1_r3_nondegenerate", "integration.rubi_4_1_1_1_r11_nondegenerate", "integration.rubi_4_1_2_1_r1_nondegenerate", "integration.rubi_4_1_7_r1_nondegenerate",
  "integration.rubi_3_1_2_r7_nondegenerate",
  "integration.linear_power_nondegenerate", "integration.constant_times_linear_nondegenerate",
  "integration.rubi_4_1_13_r11_nondegenerate", "integration.rubi_4_1_13_r12_nondegenerate",
  "integration.rubi_1_1_1_2_r1_nondegenerate", "integration.rubi_1_1_3_2_r3_nondegenerate",
  "integration.rubi_1_1_3_1_r3_nondegenerate", "integration.rubi_1_1_3_2_r6_nondegenerate",
  "integration.rubi_1_1_3_3_r10_nondegenerate", "integration.rubi_1_1_3_3_r11_nondegenerate",
  "integration.rubi_1_1_3_3_r8_nondegenerate",
  "integration.rubi_1_1_3_2_r4_nondegenerate",
  "integration.rubi_1_1_3_2_r7_nondegenerate",
  "integration.rubi_1_1_1_3_r19_nondegenerate",
  "integration.rubi_1_1_3_4_r15_nondegenerate",
  "integration.rubi_1_1_3_4_r16_nondegenerate",
  "integration.rubi_1_1_3_4_r27_nondegenerate",
  "integration.rubi_1_1_3_4_r28_nondegenerate", "integration.rubi_1_1_3_4_r29_nondegenerate",
  "integration.rubi_1_1_3_4_r14_nondegenerate",
  "integration.rubi_1_2_1_2_r4_nondegenerate", "integration.rubi_1_2_1_3_r1_nondegenerate",
  "integration.rubi_1_2_1_4_r1_nondegenerate", "integration.rubi_1_1_1_3_r2_nondegenerate",
  "integration.rubi_1_2_1_1_r3_nondegenerate", "integration.rubi_1_2_1_2_r55_nondegenerate",
  "integration.rubi_4_1_12_r81_nondegenerate", "integration.rubi_4_1_12_r82_nondegenerate",
  "integration.rubi_1_2_1_4_r65_nondegenerate", "integration.rubi_1_2_1_4_r66_nondegenerate",
  "integration.rubi_1_2_3_5_r2_nondegenerate", "integration.rubi_1_2_1_3_r14_nondegenerate",
  "integration.rubi_1_2_1_3_r13_nondegenerate", "integration.rubi_1_1_1_7_r6_nondegenerate",
  "integration.rubi_1_1_1_3_r9_nondegenerate", "integration.rubi_1_2_1_3_r25_nondegenerate",
  "integration.rubi_1_2_1_3_r24_nondegenerate", "integration.rubi_1_2_1_2_r20_nondegenerate",
  "integration.rubi_1_2_1_2_r103_nondegenerate", "integration.rubi_1_2_1_2_r104_nondegenerate",
  "integration.rubi_1_2_1_2_r1_nondegenerate", "integration.rubi_1_2_1_3_r20_nondegenerate",
  "integration.rubi_1_2_1_3_r19_nondegenerate", "integration.rubi_1_2_2_3_r7_nondegenerate",
  "integration.rubi_1_2_2_3_r8_nondegenerate", "integration.rubi_1_1_3_3_r15_nondegenerate",
  "integration.power_binomial_times_linear_nondegenerate",
  "integration.rubi_1_1_3_4_r17_nondegenerate", "integration.rubi_1_2_1_3_r35_nondegenerate",
  "integration.rubi_1_2_2_4_r11_nondegenerate", "integration.rubi_1_2_2_4_r12_nondegenerate",
  "integration.rubi_1_2_3_3_r12_nondegenerate", "integration.rubi_1_2_3_3_r19_nondegenerate",
  "integration.rubi_1_2_3_3_r20_nondegenerate",
  "integration.rubi_1_2_1_6_r5_nondegenerate", "integration.rubi_1_2_1_6_r6_nondegenerate",
  "integration.rubi_1_2_1_6_r7_nondegenerate", "integration.rubi_1_2_1_6_r8_nondegenerate",
  "integration.rubi_1_2_1_6_r10_nondegenerate",
  "integration.rubi_1_2_1_6_r9_nondegenerate", "integration.rubi_1_2_1_3_r36_nondegenerate",
  "integration.rubi_1_2_2_4_r55_nondegenerate", "integration.rubi_1_2_2_4_r56_nondegenerate",
  "integration.rubi_1_2_2_4_r57_nondegenerate", "integration.rubi_1_2_2_4_r58_nondegenerate",
  "integration.rubi_1_2_1_2_r12_nondegenerate", "integration.rubi_1_2_1_3_r16_nondegenerate",
  "integration.rubi_1_2_1_3_r15_nondegenerate", "integration.rubi_1_2_1_1_r5_nondegenerate",
  "integration.rubi_1_2_2_2_r17_nondegenerate", "integration.rubi_1_2_2_1_r5_nondegenerate",
  "integration.rubi_1_2_1_2_r102_nondegenerate", "integration.rubi_1_1_1_3_r13_nondegenerate",
  "integration.rubi_1_1_1_3_r14_nondegenerate", "integration.rubi_1_1_3_5_r24_nondegenerate",
  "integration.rubi_1_1_3_5_r25_nondegenerate", "integration.rubi_1_1_3_5_r26_nondegenerate",
  "integration.rubi_1_1_3_5_r30_nondegenerate", "integration.rubi_1_2_1_2_r43_nondegenerate",
  "integration.rubi_1_2_1_2_r44_nondegenerate", "integration.rubi_1_2_1_2_r45_nondegenerate",
  "integration.rubi_1_2_1_2_r54_nondegenerate",
  "integration.rubi_4_7_9_r1_nondegenerate", "integration.rubi_4_7_9_r2_nondegenerate",
  "integration.rubi_4_7_9_r25_nondegenerate", "integration.rubi_4_7_9_r26_nondegenerate",
  "integration.rubi_4_7_6_r1_nondegenerate", "integration.rubi_4_7_6_r2_nondegenerate",
  "integration.rubi_4_7_6_r16_nondegenerate", "integration.rubi_4_7_6_r17_nondegenerate",
  "integration.rubi_4_1_13_r1_nondegenerate", "integration.rubi_4_1_13_r2_nondegenerate", "integration.rubi_4_1_13_r13_nondegenerate", "integration.rubi_4_1_13_r14_nondegenerate", "integration.rubi_4_1_13_r19_nondegenerate",
  "integration.rubi_4_1_13_r20_nondegenerate", "integration.rubi_4_1_13_r15_nondegenerate", "integration.rubi_4_1_13_r16_nondegenerate", "integration.rubi_4_1_13_r21_nondegenerate", "integration.rubi_4_1_13_r22_nondegenerate",
  "integration.rubi_4_7_9_r11_nondegenerate", "integration.rubi_4_7_9_r12_nondegenerate",
  "integration.rubi_2_3_r32_nondegenerate", "integration.rubi_2_3_r33_nondegenerate",
  "integration.rubi_3_1_4_r17_nondegenerate", "integration.rubi_3_1_5_r16_nondegenerate",
  "integration.rubi_3_1_5_r13_nondegenerate", "integration.rubi_3_1_4_r9_nondegenerate",
  "integration.rubi_3_1_4_r18_nondegenerate", "integration.rubi_3_1_5_r17_nondegenerate",
  "integration.rubi_4_7_9_r16_nondegenerate", "integration.rubi_4_7_9_r27_nondegenerate",
  "integration.rubi_4_7_9_r30_nondegenerate", "integration.rubi_4_1_12_r33_nondegenerate",
  "integration.rubi_4_1_12_r34_nondegenerate",
  "integration.rubi_1_2_3_1_r5_nondegenerate",
  "integration.rubi_2_1_r9_nondegenerate", "integration.rubi_2_1_r10_nondegenerate",
  "integration.rubi_4_1_12_r43_nondegenerate", "integration.rubi_4_1_12_r44_nondegenerate",
  "integration.two_linear_factors_times_powers_nondegenerate", "integration.rubi_1_1_1_4_r3_nondegenerate",
  "integration.rubi_1_2_1_3_r33_nondegenerate", "integration.rubi_1_1_3_3_r16_nondegenerate",
  "integration.rubi_1_1_3_4_r25_nondegenerate",
  "integration.linear_factor_over_linear_nondegenerate", "integration.power_ratio_split_nondegenerate",
  "integration.partial_fractions_general_nondegenerate", "integration.product_over_trinomial_nondegenerate",
  "integration.product_over_quadratic_nondegenerate", "integration.linear_times_two_powers_nondegenerate",
  "integration.linear_times_trinomial_power_nondegenerate", "integration.binomial_ratio_negative_power_nondegenerate",
  "integration.linear_times_quadratic_power_nondegenerate", "integration.linear_sin_trinomial_nondegenerate",
  "integration.linear_cos_trinomial_nondegenerate", "integration.sin_trinomial_square_nondegenerate",
  "integration.cos_trinomial_square_nondegenerate",
  "integration.rubi_1_1_3_3_r18_nondegenerate",
  "integration.rubi_1_2_1_2_r5_nondegenerate", "integration.rubi_1_2_3_3_r50_nondegenerate",
  "integration.rubi_4_1_12_r45_nondegenerate", "integration.rubi_4_1_12_r46_nondegenerate",
  "integration.rubi_4_1_12_r53_nondegenerate", "integration.rubi_4_1_12_r54_nondegenerate",
  "integration.rubi_1_2_1_2_r46_nondegenerate",
  "integration.rubi_1_2_1_2_r96_nondegenerate", "integration.rubi_1_2_3_3_r27_nondegenerate",
  "integration.rubi_1_2_3_4_r40_nondegenerate", "integration.rubi_1_2_3_4_r34_nondegenerate",
  "integration.rubi_1_2_3_4_r38_nondegenerate", "integration.rubi_1_2_3_2_r10_nondegenerate",
  "integration.rubi_1_2_3_2_r18_nondegenerate",
  "integration.rubi_1_2_3_4_r64_nondegenerate", "integration.rubi_1_2_3_4_r61_nondegenerate",
  "integration.rubi_1_2_1_3_r26_nondegenerate", "integration.rubi_1_1_3_3_r5_nondegenerate",
  "integration.rubi_1_1_3_7_r5_nondegenerate",
  "integration.rubi_1_2_2_4_r59_nondegenerate", "integration.rubi_1_2_2_4_r60_nondegenerate",
  "integration.rubi_1_2_2_4_r61_nondegenerate", "integration.rubi_1_2_2_4_r62_nondegenerate",
  "integration.rubi_1_1_1_3_r53_nondegenerate",
  "integration.rubi_1_3_1_r4_nondegenerate", "integration.rubi_1_3_2_r1_nondegenerate",
  "integration.rubi_2_3_r11_nondegenerate", "integration.rubi_2_3_r23_nondegenerate",
  "integration.rubi_2_3_r24_nondegenerate", "integration.rubi_2_3_r26_nondegenerate",
  "integration.rubi_2_3_r35_nondegenerate"]

#guard strengthenedIds.all fun id =>
  match Integration.catalogVerified.find? (·.rule.id == id) with
  | none => false
  | some v =>
    match Integration.catalog.find? (·.rule.id ++ "_nondegenerate" == id) with
    | none => false
    | some o =>
      o.rule.legacyId == v.rule.legacyId && o.proofs.isEmpty &&
      o.rule.body == v.rule.body && o.rule.result == v.rule.result &&
      o.rule.conditions.length < v.rule.conditions.length &&
      v.rule.conditions.take o.rule.conditions.length == o.rule.conditions &&
      [Domain.real, Domain.complex].all fun d => (v.proofs.lookup d).isSome

-- Strengthened variants proved over ℝ only: the complex domain stays unproved
-- and a `domain:` finding replaces the `numerical:` one.
private def strengthenedRealIds : List String := [
  "integration.rubi_4_5_4_2_r15_nondegenerate", "integration.rubi_4_5_4_2_r16_nondegenerate", "integration.rubi_4_5_1_2_r26_nondegenerate", "integration.rubi_4_7_6_r19_nondegenerate", "integration.rubi_4_7_6_r21_nondegenerate", "integration.rubi_4_7_6_r9_nondegenerate",
  "integration.rubi_5_3_3_r9_nondegenerate", "integration.rubi_5_3_4_r103_nondegenerate",
  "integration.rubi_4_5_4_1_r14_nondegenerate", "integration.rubi_4_5_4_1_r15_nondegenerate", "integration.rubi_4_5_1_2_r50_nondegenerate", "integration.rubi_4_5_3_1_r14_nondegenerate", "integration.rubi_4_5_3_1_r15_nondegenerate", "integration.rubi_4_5_3_1_r8_nondegenerate", "integration.rubi_4_5_4_1_r6_nondegenerate", "integration.rubi_4_5_4_2_r10_nondegenerate", "integration.rubi_4_5_4_2_r11_nondegenerate", "integration.rubi_4_5_4_2_r12_nondegenerate", "integration.rubi_4_5_4_2_r19_nondegenerate", "integration.rubi_4_5_4_2_r20_nondegenerate", "integration.rubi_4_5_4_2_r21_nondegenerate", "integration.rubi_4_5_4_2_r22_nondegenerate", "integration.rubi_4_5_4_2_r9_nondegenerate", "integration.rubi_4_5_3_1_r2_nondegenerate", "integration.rubi_4_5_4_2_r5_nondegenerate", "integration.rubi_4_5_4_2_r6_nondegenerate",
  "integration.rubi_4_5_3_1_r12_nondegenerate", "integration.rubi_4_5_3_1_r43_nondegenerate",
  "integration.rubi_4_5_4_1_r2_nondegenerate", "integration.rubi_4_5_4_2_r2_nondegenerate", "integration.rubi_4_5_4_2_r1_nondegenerate",
  "integration.rubi_4_5_2_1_r17_nondegenerate", "integration.rubi_4_5_4_1_r8_nondegenerate", "integration.rubi_4_5_4_1_r9_nondegenerate", "integration.rubi_6_7_8_r47_nondegenerate", "integration.rubi_6_7_8_r48_nondegenerate", "integration.rubi_6_3_12_r3_nondegenerate",
  "integration.rubi_4_7_9_r31_nondegenerate", "integration.rubi_4_7_9_r32_nondegenerate", "integration.rubi_6_7_9_r26_nondegenerate", "integration.rubi_6_7_9_r27_nondegenerate", "integration.rubi_6_7_9_r28_nondegenerate", "integration.rubi_6_7_9_r29_nondegenerate", "integration.rubi_6_7_9_r31_nondegenerate", "integration.rubi_6_7_9_r32_nondegenerate", "integration.rubi_6_7_9_r33_nondegenerate", "integration.rubi_6_7_9_r34_nondegenerate",
  "integration.rubi_1_1_3_5_r12_nondegenerate", "integration.rubi_1_2_1_7_r29_nondegenerate", "integration.rubi_1_2_1_7_r30_nondegenerate", "integration.rubi_1_2_1_7_r31_nondegenerate", "integration.rubi_1_2_1_7_r32_nondegenerate",
  "integration.rubi_4_7_9_r21_nondegenerate", "integration.rubi_4_7_9_r22_nondegenerate", "integration.rubi_6_7_9_r19_nondegenerate", "integration.rubi_6_7_9_r20_nondegenerate", "integration.rubi_6_7_9_r13_nondegenerate", "integration.rubi_4_7_9_r13_nondegenerate", "integration.rubi_4_7_9_r14_nondegenerate", "integration.rubi_6_7_9_r11_nondegenerate", "integration.rubi_6_7_9_r12_nondegenerate",
  "integration.rubi_4_5_4_1_r1_nondegenerate",
  "integration.rubi_4_5_9_r11_nondegenerate", "integration.rubi_4_5_9_r12_nondegenerate", "integration.rubi_4_5_9_r5_nondegenerate", "integration.rubi_4_5_9_r6_nondegenerate",
  "integration.rubi_4_5_4_1_r10_nondegenerate", "integration.rubi_4_5_3_1_r3_nondegenerate", "integration.rubi_4_5_1_2_r52_nondegenerate", "integration.rubi_4_1_7_r4_nondegenerate",
  "integration.rubi_4_5_9_r1_nondegenerate", "integration.rubi_4_5_9_r2_nondegenerate",
  "integration.rubi_4_5_4_1_r7_nondegenerate", "integration.rubi_4_5_1_2_r2_nondegenerate",
  "integration.rubi_4_5_1_2_r3_nondegenerate", "integration.rubi_4_5_1_2_r4_nondegenerate", "integration.rubi_4_5_10_r5_nondegenerate",
  "integration.rubi_4_5_7_r6_nondegenerate", "integration.rubi_4_5_1_1_r17_nondegenerate", "integration.rubi_4_5_1_2_r45_nondegenerate", "integration.rubi_4_5_1_2_r1_nondegenerate",
  "integration.rubi_7_2_6_r2_nondegenerate", "integration.rubi_7_2_3_r4_nondegenerate", "integration.rubi_7_2_3_r5_nondegenerate",
  "integration.rubi_7_2_2_r2_nondegenerate", "integration.rubi_7_2_5_r2_nondegenerate", "integration.rubi_7_2_6_r1_nondegenerate", "integration.rubi_7_2_1_r2_nondegenerate", "integration.rubi_7_2_1_r3_nondegenerate", "integration.rubi_7_2_2_r6_nondegenerate", "integration.rubi_7_2_2_r1_nondegenerate",
  "integration.rubi_7_1_6_r2_nondegenerate",
  "integration.rubi_7_1_3_r2_nondegenerate", "integration.rubi_7_1_4_r23_nondegenerate", "integration.rubi_7_1_5_r11_nondegenerate",
  "integration.rubi_7_1_6_r1_nondegenerate", "integration.rubi_7_1_1_r2_nondegenerate", "integration.rubi_7_1_1_r3_nondegenerate", "integration.rubi_7_1_3_r7_nondegenerate", "integration.rubi_7_1_4_r1_nondegenerate", "integration.rubi_7_1_2_r6_nondegenerate", "integration.rubi_7_1_2_r2_nondegenerate", "integration.rubi_7_1_5_r2_nondegenerate",
  "integration.rubi_7_3_1_r164_nondegenerate", "integration.rubi_7_3_4_r144_nondegenerate",
  "integration.rubi_7_3_7_r37_nondegenerate", "integration.rubi_7_3_4_misc_r37_nondegenerate", "integration.rubi_7_3_7_r38_nondegenerate", "integration.rubi_7_3_4_misc_r38_nondegenerate", "integration.rubi_7_3_7_r39_nondegenerate", "integration.rubi_7_3_4_misc_r39_nondegenerate", "integration.rubi_7_3_7_r40_nondegenerate", "integration.rubi_7_3_4_misc_r40_nondegenerate",
  "integration.rubi_7_3_1_r31_nondegenerate", "integration.rubi_7_3_4_r11_nondegenerate", "integration.rubi_7_3_1_r51_nondegenerate", "integration.rubi_7_3_4_r31_nondegenerate",
  "integration.rubi_7_3_1_r7_nondegenerate", "integration.rubi_7_3_1_r8_nondegenerate", "integration.rubi_7_3_2_r7_nondegenerate", "integration.rubi_7_3_5_r7_nondegenerate", "integration.rubi_7_3_2_r8_nondegenerate", "integration.rubi_7_3_5_r8_nondegenerate", "integration.rubi_7_3_1_r9_nondegenerate", "integration.rubi_7_3_3_r1_nondegenerate", "integration.rubi_7_3_5_r6_nondegenerate", "integration.rubi_7_3_2_r6_b_nondegenerate",
  "integration.rubi_7_3_7_r33_nondegenerate", "integration.rubi_7_3_4_misc_r33_nondegenerate", "integration.rubi_7_3_7_r34_nondegenerate", "integration.rubi_7_3_4_misc_r34_nondegenerate",
  "integration.rubi_7_3_1_r39_nondegenerate", "integration.rubi_7_3_4_r19_nondegenerate",
  "integration.rubi_7_3_7_r45_nondegenerate", "integration.rubi_7_3_4_misc_r45_nondegenerate",
  "integration.rubi_7_3_7_r21_nondegenerate", "integration.rubi_7_3_4_misc_r21_nondegenerate", "integration.rubi_7_3_7_r17_nondegenerate", "integration.rubi_7_3_4_misc_r17_nondegenerate",
  "integration.rubi_7_3_2_r1_nondegenerate", "integration.rubi_7_3_5_r1_nondegenerate", "integration.rubi_7_3_2_r2_nondegenerate", "integration.rubi_7_3_5_r2_nondegenerate", "integration.rubi_7_3_5_r5_nondegenerate", "integration.rubi_7_3_2_r5_b_nondegenerate", "integration.rubi_7_3_2_r9_nondegenerate", "integration.rubi_7_3_5_r9_nondegenerate", "integration.rubi_7_3_2_r10_nondegenerate", "integration.rubi_7_3_5_r10_nondegenerate", "integration.rubi_7_3_1_pow_r5_nondegenerate", "integration.rubi_7_3_2_r13_nondegenerate",
  "integration.rubi_7_3_1_r172_nondegenerate", "integration.rubi_7_3_2_r5_nondegenerate", "integration.rubi_7_3_1_r173_nondegenerate", "integration.rubi_7_3_2_r6_nondegenerate",
  "integration.rubi_7_3_1_r21_nondegenerate", "integration.rubi_7_3_4_r1_nondegenerate",
  "integration.rubi_7_3_1_r136_nondegenerate", "integration.rubi_7_3_4_r116_nondegenerate",
  "integration.rubi_7_3_1_r82_nondegenerate", "integration.rubi_7_3_4_r62_nondegenerate",
  "integration.rubi_7_3_1_r118_nondegenerate", "integration.rubi_7_3_4_r98_nondegenerate",
  "integration.rubi_7_3_1_r89_nondegenerate", "integration.rubi_7_3_4_r69_nondegenerate",
  "integration.rubi_7_3_1_r101_nondegenerate", "integration.rubi_7_3_4_r81_nondegenerate",
  "integration.rubi_7_3_1_r94_nondegenerate", "integration.rubi_7_3_4_r74_nondegenerate",
  "integration.rubi_7_3_1_r87_nondegenerate", "integration.rubi_7_3_4_r67_nondegenerate",
  "integration.rubi_7_3_1_r83_nondegenerate", "integration.rubi_7_3_4_r63_nondegenerate",
  "integration.rubi_7_3_1_r43_nondegenerate", "integration.rubi_7_3_4_r23_nondegenerate", "integration.rubi_7_3_1_r44_nondegenerate", "integration.rubi_7_3_4_r24_nondegenerate",
  "integration.rubi_7_3_1_r85_nondegenerate", "integration.rubi_7_3_4_r65_nondegenerate", "integration.rubi_7_3_1_r86_nondegenerate", "integration.rubi_7_3_4_r66_nondegenerate",
  "integration.rubi_7_3_1_r65_nondegenerate", "integration.rubi_7_3_4_r45_nondegenerate", "integration.rubi_7_3_1_r67_nondegenerate", "integration.rubi_7_3_4_r47_nondegenerate", "integration.rubi_7_3_1_r66_nondegenerate", "integration.rubi_7_3_4_r46_nondegenerate", "integration.rubi_7_3_1_r68_nondegenerate", "integration.rubi_7_3_4_r48_nondegenerate",
  "integration.rubi_7_3_1_r70_nondegenerate", "integration.rubi_7_3_1_r74_nondegenerate", "integration.rubi_7_3_1_r80_nondegenerate", "integration.rubi_7_3_4_r50_nondegenerate", "integration.rubi_7_3_4_r54_nondegenerate", "integration.rubi_7_3_4_r60_nondegenerate",
  "integration.rubi_7_3_1_r17_nondegenerate", "integration.rubi_7_3_3_r9_nondegenerate", "integration.rubi_7_3_1_r123_nondegenerate", "integration.rubi_7_3_4_r103_nondegenerate", "integration.rubi_7_3_1_r124_nondegenerate", "integration.rubi_7_3_4_r104_nondegenerate", "integration.rubi_7_3_1_r18_nondegenerate", "integration.rubi_7_3_3_r10_nondegenerate", "integration.rubi_7_3_1_r29_nondegenerate", "integration.rubi_7_3_4_r9_nondegenerate", "integration.rubi_7_3_1_r47_nondegenerate", "integration.rubi_7_3_4_r27_nondegenerate", "integration.rubi_7_3_1_r69_nondegenerate", "integration.rubi_7_3_1_r73_nondegenerate", "integration.rubi_7_3_1_r79_nondegenerate", "integration.rubi_7_3_4_r49_nondegenerate", "integration.rubi_7_3_4_r53_nondegenerate", "integration.rubi_7_3_4_r59_nondegenerate",
  "integration.rubi_7_3_1_r35_nondegenerate", "integration.rubi_7_3_4_r15_nondegenerate", "integration.rubi_7_3_1_r36_nondegenerate", "integration.rubi_7_3_4_r16_nondegenerate",
  "integration.rubi_4_5_1_1_r4_nondegenerate", "integration.rubi_5_3_6_r13_nondegenerate", "integration.rubi_5_3_6_r55_nondegenerate", "integration.rubi_5_3_4_r15_nondegenerate", "integration.rubi_5_3_4_r16_nondegenerate",
  "integration.rubi_3_1_1_r3_nondegenerate", "integration.rubi_3_1_2_r5_nondegenerate",
  "integration.rubi_3_1_2_r6_nondegenerate", "integration.rubi_3_1_4_r12_nondegenerate",
  "integration.rubi_3_1_5_r8_nondegenerate", "integration.rubi_3_1_4_r2_nondegenerate",
  "integration.rubi_3_1_5_r3_nondegenerate", "integration.log_power_over_linear_square_nondegenerate",
  "integration.rubi_3_1_3_r1_nondegenerate", "integration.rubi_3_1_3_r10_nondegenerate",
  "integration.rubi_3_1_4_r13_nondegenerate", "integration.rubi_3_1_5_r9_nondegenerate",
  "integration.rubi_3_1_3_r7_nondegenerate", "integration.rubi_4_7_8_r47_nondegenerate",
  "integration.rubi_4_7_8_r48_nondegenerate", "integration.rubi_3_1_2_r3_nondegenerate",
  "integration.rubi_3_1_5_r28_nondegenerate", "integration.rubi_3_5_r16_nondegenerate",
  "integration.rubi_3_5_r21_nondegenerate",
  "integration.rubi_4_7_8_r13_nondegenerate", "integration.rubi_4_7_8_r14_nondegenerate",
  "integration.rubi_3_4_r2_nondegenerate", "integration.rubi_3_2_1_r1_nondegenerate",
  "integration.rubi_3_3_r22_nondegenerate",
  "integration.log_linear_over_x_nondegenerate", "integration.power_log_linear_nondegenerate",
  "integration.power_sin_log_nondegenerate", "integration.power_cos_log_nondegenerate",
  "integration.sin_x_log_times_log_nondegenerate", "integration.cos_x_log_times_log_nondegenerate",
  "integration.linear_power_log_linear_nondegenerate", "integration.power_log_ratio_nondegenerate",
  "integration.rubi_3_5_r23_nondegenerate", "integration.rubi_3_2_1_r2_nondegenerate",
  "integration.log_product_power_nondegenerate", "integration.power_log_product_nondegenerate",
  "integration.power_log_product_power_nondegenerate",
  "integration.rubi_3_1_4_r10_nondegenerate", "integration.rubi_3_1_4_r22_nondegenerate",
  "integration.rubi_3_3_r12_nondegenerate", "integration.rubi_3_2_3_r8_nondegenerate",
  "integration.log_monomial_log_linear_over_x_nondegenerate", "integration.rubi_3_3_r31_nondegenerate",
  "integration.rubi_3_1_5_r33_nondegenerate", "integration.power_two_log_linear_nondegenerate",
  "integration.log_power_log_binomial_over_x_nondegenerate", "integration.power_log_log_nondegenerate",
  "integration.power_log_monomial_log_linear_nondegenerate",
  "integration.power_log_binomial_nondegenerate"]

#guard strengthenedRealIds.all fun id =>
  match Integration.catalogVerified.find? (·.rule.id == id) with
  | none => false
  | some v =>
    match Integration.catalog.find? (·.rule.id ++ "_nondegenerate" == id) with
    | none => false
    | some o =>
      o.rule.legacyId == v.rule.legacyId && o.proofs.isEmpty &&
      o.rule.body == v.rule.body && o.rule.result == v.rule.result &&
      o.rule.conditions.length < v.rule.conditions.length &&
      v.rule.conditions.take o.rule.conditions.length == o.rule.conditions &&
      (v.proofs.lookup .real).isSome && (v.proofs.lookup .complex).isNone &&
      v.unproved == [.complex] && v.findings.any (·.startsWith "domain:")

#guard
  let ids := (Integration.catalogVerified.filter fun e =>
    e.findings.any (·.startsWith "strengthened:")).map (·.rule.id)
  ids.length == (strengthenedIds ++ strengthenedRealIds).length + 1 &&
    (strengthenedIds ++ strengthenedRealIds).all ids.contains &&
    ids.contains "integration.rubi_3_1_2_r2_nondegenerate"

-- The order-free generalization is published independently; the original
-- strengthened rule retains its ordering conditions and its own proof.
#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_4_r16_order_free") with
  | none => false
  | some v =>
    v.findings.any (·.startsWith "generalized:") &&
    v.proofs == [(.real, ``OSR.IntegrationRec203.rubi1134r16OrderFree_real),
      (.complex, ``OSR.IntegrationRec203.rubi1134r16OrderFree_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    !(v.rule.symbols.contains ⟨"relation1", "gt"⟩) &&
    (OSR.Registry.mappingAssurance v.rule.symbols .complex).certifiable

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_4_r27_order_free") with
  | none => false
  | some v =>
    v.findings.any (·.startsWith "generalized:") &&
    v.proofs == [(.real, ``OSR.IntegrationRec204.rubi1134r27OrderFree_real),
      (.complex, ``OSR.IntegrationRec204.rubi1134r27OrderFree_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    !(v.rule.symbols.contains ⟨"relation1", "gt"⟩) &&
    (OSR.Registry.mappingAssurance v.rule.symbols .complex).certifiable

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_4_r28_order_free") with
  | none => false
  | some v =>
    v.findings.any (·.startsWith "generalized:") &&
    v.proofs == [(.real, ``OSR.IntegrationRec205.rubi1134r28OrderFree_real),
      (.complex, ``OSR.IntegrationRec205.rubi1134r28OrderFree_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    !(v.rule.symbols.contains ⟨"relation1", "gt"⟩) &&
    (OSR.Registry.mappingAssurance v.rule.symbols .complex).certifiable

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_4_r29_order_free") with
  | none => false
  | some v =>
    v.findings.any (·.startsWith "generalized:") &&
    v.proofs == [(.real, ``OSR.IntegrationRec206.rubi1134r29OrderFree_real),
      (.complex, ``OSR.IntegrationRec206.rubi1134r29OrderFree_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    !(v.rule.symbols.contains ⟨"relation1", "gt"⟩) &&
    (OSR.Registry.mappingAssurance v.rule.symbols .complex).certifiable

-- Direct proofs promote these rules from `IntegrationNum1` into the verified
-- catalogue, with both domain theorems attached.
#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_3_1_2_r7_nondegenerate") with
  | none => false
  | some v =>
    v.proofs == [(.real, ``OSR.IntegrationRec209.rubi312r7Nondeg_real),
      (.complex, ``OSR.IntegrationRec209.rubi312r7Nondeg_complex)] &&
    v.unproved.isEmpty && v.counterexamples.isEmpty &&
    (OSR.Registry.mappingAssurance v.rule.symbols .real).certifiable &&
    (OSR.Registry.mappingAssurance v.rule.symbols .complex).certifiable

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_3_1_2_r2_nondegenerate") with
  | none => false
  | some v =>
    v.proofs == [(.real, ``OSR.IntegrationRec207.rubi312r2Nondeg_real)] &&
    v.unproved.isEmpty &&
    v.counterexamples == [(.complex, ``OSR.IntegrationRec208.rubi312r2Nondeg_counterexample_complex)] &&
    (OSR.Registry.mappingAssurance v.rule.symbols .real).certifiable

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_3_r11_nondegenerate") with
  | none => false
  | some v =>
    v.proofs == [(.real, ``OSR.IntegrationRec197.rubi1133r11Nondeg_real),
      (.complex, ``OSR.IntegrationRec197.rubi1133r11Nondeg_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    v.findings.any (·.startsWith "strengthened:")

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_3_r8_nondegenerate") with
  | none => false
  | some v =>
    v.proofs == [(.real, ``OSR.IntegrationRec198.rubi1133r8Nondeg_real),
      (.complex, ``OSR.IntegrationRec198.rubi1133r8Nondeg_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty &&
    v.findings.any (·.startsWith "strengthened:")

#guard
  match Integration.catalogVerified.find? (·.rule.id == "integration.rubi_1_1_3_2_r4_nondegenerate") with
  | none => false
  | some v =>
    v.proofs == [(.real, ``OSR.IntegrationRec199.rubi1132r4Nondeg_real),
      (.complex, ``OSR.IntegrationRec199.rubi1132r4Nondeg_complex)] &&
    v.counterexamples.isEmpty && v.unproved.isEmpty

-- The remaining strengthened variants checked numerically
-- (`OSR.IntegrationNum1`) remain distributed unproved.
#guard Integration.pendingEntries.length == 424
#guard Integration.pendingEntries.all fun v =>
  v.proofs.isEmpty && v.counterexamples.isEmpty && v.unproved == [.real, .complex] &&
  v.findings.any (·.startsWith "strengthened:") && v.findings.any (·.startsWith "numerical:") &&
  match Integration.catalogVerified.find? (·.rule.id ++ "_nondegenerate" == v.rule.id) with
  | none => false
  | some o =>
    o.rule.legacyId == v.rule.legacyId && o.proofs.isEmpty &&
    o.rule.body == v.rule.body && o.rule.result == v.rule.result &&
    o.rule.integrals == v.rule.integrals && o.rule.substs == v.rule.substs &&
    o.rule.conditions.length < v.rule.conditions.length &&
    v.rule.conditions.take o.rule.conditions.length == o.rule.conditions

-- Identifiers are unique, every rule is well formed and has the antiderivative shape.
#guard (Integration.catalog.map (·.rule.id)).eraseDups.length == Integration.catalog.length
#guard Integration.catalog.all fun e =>
  match e.rule.legacyId with
  | none => false
  | some id => Integration.notMigrated.all fun entry => entry.1 != id
#guard Integration.catalog.all fun e =>
  if e.rule.shape == .antiderivRec || e.rule.shape == .antiderivSubst then e.rule.recOk
  else e.rule.wellFormed
#guard Integration.catalog.all (·.rule.recOk)
#guard Integration.catalog.all fun e => e.rule.shape == .antideriv ||
  e.rule.shape == .antiderivRec || e.rule.shape == .antiderivSubst
#guard Integration.catalog.all (·.rule.conditionsOk)
#guard Calculus.catalog.all (·.rule.conditionsOk)

-- Conditions are exported as relation1#neq.
#guard power.symbols.contains ⟨"relation1", "neq"⟩

-- A residual integral is exported as int(λx. H)(x).
#guard match IntegrationRec.sinAddSq.replacementOM with
  | .ombind b ["x"] (.oma _ [.oma _ [_, .omapp (.oma h [.ombind b' ["x"] _]) [.omv "x"]], _]) =>
    b == lambdaSymbol && h == intSymbol && b' == lambdaSymbol
  | _ => false

-- Recursive rules are not applied by the reference rewriter.
#guard (rewrite (Integration.catalog.map (·.rule))
  (.integral "t" (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d")
    (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") t)) (.int 2))))))).isNone

-- Every migrated rule is proved or refuted in at least one domain (a few
-- numerically found counterexamples are established over ℂ only).
#guard Integration.catalogVerified.all fun e =>
  [Domain.real, Domain.complex].any fun d =>
    (e.proofs.lookup d).isSome || (e.counterexamples.lookup d).isSome

-- No Calculus rule has the antiderivative shape: the Calculus set is unchanged.
#guard Calculus.catalog.all (·.rule.shape != .antideriv)

-- The exported pattern is calculus1#int applied to a lambda.
#guard match constant.patternOM with
  | .oma h [.ombind b ["x"] _] => h == intSymbol && b == lambdaSymbol
  | _ => false
#guard constant.symbols.contains intSymbol

private def rules : List CRule :=
  (Integration.catalog.filter fun e => (e.proofs.lookup .real).isSome).map (·.rule)

-- The rules proved over ℝ; the reference rewriter applies the unconditional ones.
#guard rules.map (·.id) == ["integration.log_monomial", "integration.constant",
  "integration.power", "integration.sin_log", "integration.cos_log",
  "integration.sin_add_square", "integration.cos_add_square",
  "integration.sin_add_power_over_x", "integration.cos_add_power_over_x",
  "integration.power_sin_square", "integration.power_cos_square",
  "integration.log_linear_power", "integration.partial_fractions_linear",
  "integration.partial_fractions_power", "integration.split_linear_factor_binomial",
  "integration.split_linear_factor_quadratic",
  "integration.partial_fractions_linear_quadratic",
  "integration.partial_fractions_linear_trinomial",
  "integration.partial_fractions_power_weighted", "integration.sin_cos_double_angle",
  "integration.split_log_linear_factor", "integration.linear_power_over_quadratic",
  "integration.binomial_negative_power", "integration.binomial_power_sin",
  "integration.binomial_power_cos", "integration.monomial_binomial_power_sin",
  "integration.monomial_binomial_power_cos",
  "integration.split_power_linear_log_over_x", "integration.power_sin_power_by_parts",
  "integration.power_cos_power_by_parts", "integration.power_over_trig_squares",
  "integration.power_log_times_power_log", "integration.quadratic_power_log_by_parts",
  "integration.split_power_linear_log_over_x_monomial", "integration.sin_power_log_reduction",
  "integration.cos_power_log_reduction", "integration.power_sin_power_reduction",
  "integration.power_cos_power_reduction", "integration.quadratic_power_reduction",
  "integration.linear_quadratic_power_reduction", "integration.quartic_power_reduction",
  "integration.linear_linear_power", "integration.monomial_binomial_power_by_parts",
  "integration.linear_linear_reciprocal", "integration.linear_linear_monomial_power", "integration.power_inverse_linear_log",
  "integration.power_inverse_linear_log_u", "integration.power_inverse_linear_log_linear",
  "integration.polynomial_binomial_split", "integration.polynomial_binomial_binomial_split",
  "integration.cos_power_over_sin_binomial", "integration.sin_power_over_cos_binomial",
  "integration.exp_one_plus_cos_power", "integration.exp_one_minus_cos_power",
  "integration.exp_linear_cos_over_sin", "integration.exp_linear_sin_over_cos",
  "integration.monomial_over_log_scale", "integration.sin_square_over_sin_x_cos_square",
  "integration.log_quotient_split", "integration.linear_quadratic_power_eq_reduction",
  "integration.monomial_binomial_pair_by_parts", "integration.improper_trinomial_equal_powers",
  "integration.monomial_improper_trinomial_equal_powers", "integration.trinomial_negative_power",
  "integration.partial_fractions_monomial_binomial_pair",
  "integration.binomial_triple_negative_flip",
  "integration.monomial_binomial_triple_negative_flip",
  "integration.binomial_triple_positive_flip", "integration.monomial_binomial_triple_positive_flip",
  "integration.linear_split_binomial_trinomial", "integration.linear_split_binomial_binomial",
  "integration.linear_power_nondegenerate", "integration.constant_times_linear_nondegenerate",
  "integration.rubi_4_1_13_r11_nondegenerate", "integration.rubi_4_1_13_r12_nondegenerate",
  "integration.rubi_1_1_1_2_r1_nondegenerate", "integration.rubi_1_1_3_2_r3_nondegenerate",
  "integration.rubi_1_1_3_1_r3_nondegenerate", "integration.rubi_1_1_3_2_r6_nondegenerate",
  "integration.rubi_1_1_3_3_r10_nondegenerate", "integration.rubi_1_1_3_3_r11_nondegenerate",
  "integration.rubi_1_1_3_3_r8_nondegenerate",
  "integration.rubi_1_1_3_2_r4_nondegenerate",
  "integration.rubi_1_1_3_2_r7_nondegenerate",
  "integration.rubi_1_1_1_3_r19_nondegenerate",
  "integration.rubi_1_1_3_4_r15_nondegenerate",
  "integration.rubi_1_1_3_4_r16_nondegenerate",
  "integration.rubi_1_1_3_4_r27_nondegenerate",
  "integration.rubi_1_1_3_4_r28_nondegenerate", "integration.rubi_1_1_3_4_r29_nondegenerate",
  "integration.rubi_1_1_3_4_r16_order_free",
  "integration.rubi_1_1_3_4_r27_order_free",
  "integration.rubi_1_1_3_4_r28_order_free",
  "integration.rubi_1_1_3_4_r29_order_free",
  "integration.rubi_1_1_3_4_r14_nondegenerate",
  "integration.rubi_1_2_1_2_r4_nondegenerate", "integration.rubi_1_2_1_3_r1_nondegenerate",
  "integration.rubi_1_2_1_4_r1_nondegenerate", "integration.rubi_1_1_1_3_r2_nondegenerate",
  "integration.rubi_1_2_1_1_r3_nondegenerate", "integration.rubi_1_2_1_2_r55_nondegenerate",
  "integration.rubi_4_1_12_r81_nondegenerate", "integration.rubi_4_1_12_r82_nondegenerate",
  "integration.rubi_1_2_1_4_r65_nondegenerate", "integration.rubi_1_2_1_4_r66_nondegenerate",
  "integration.rubi_1_2_3_5_r2_nondegenerate", "integration.rubi_1_2_1_3_r14_nondegenerate",
  "integration.rubi_1_2_1_3_r13_nondegenerate", "integration.rubi_1_1_1_7_r6_nondegenerate",
  "integration.rubi_1_1_1_3_r9_nondegenerate", "integration.rubi_1_2_1_3_r25_nondegenerate",
  "integration.rubi_1_2_1_3_r24_nondegenerate", "integration.rubi_1_2_1_2_r20_nondegenerate",
  "integration.rubi_1_2_1_2_r103_nondegenerate", "integration.rubi_1_2_1_2_r104_nondegenerate",
  "integration.rubi_1_2_1_2_r1_nondegenerate", "integration.rubi_1_2_1_3_r20_nondegenerate",
  "integration.rubi_1_2_1_3_r19_nondegenerate", "integration.rubi_1_2_2_3_r7_nondegenerate",
  "integration.rubi_1_2_2_3_r8_nondegenerate", "integration.rubi_1_1_3_3_r15_nondegenerate",
  "integration.power_binomial_times_linear_nondegenerate",
  "integration.rubi_1_1_3_4_r17_nondegenerate", "integration.rubi_1_2_1_3_r35_nondegenerate",
  "integration.rubi_1_2_2_4_r11_nondegenerate", "integration.rubi_1_2_2_4_r12_nondegenerate",
  "integration.rubi_1_2_3_3_r12_nondegenerate", "integration.rubi_1_2_3_3_r19_nondegenerate",
  "integration.rubi_1_2_3_3_r20_nondegenerate",
  "integration.rubi_1_2_1_6_r5_nondegenerate", "integration.rubi_1_2_1_6_r6_nondegenerate",
  "integration.rubi_1_2_1_6_r7_nondegenerate", "integration.rubi_1_2_1_6_r8_nondegenerate",
  "integration.rubi_1_2_1_6_r10_nondegenerate",
  "integration.rubi_1_2_1_6_r9_nondegenerate", "integration.rubi_1_2_1_3_r36_nondegenerate",
  "integration.rubi_1_2_2_4_r55_nondegenerate", "integration.rubi_1_2_2_4_r56_nondegenerate",
  "integration.rubi_1_2_2_4_r57_nondegenerate", "integration.rubi_1_2_2_4_r58_nondegenerate",
  "integration.rubi_1_2_1_2_r12_nondegenerate", "integration.rubi_1_2_1_3_r16_nondegenerate",
  "integration.rubi_1_2_1_3_r15_nondegenerate", "integration.rubi_1_2_1_1_r5_nondegenerate",
  "integration.rubi_1_2_2_2_r17_nondegenerate", "integration.rubi_1_2_2_1_r5_nondegenerate",
  "integration.rubi_1_2_1_2_r102_nondegenerate", "integration.rubi_1_1_1_3_r13_nondegenerate",
  "integration.rubi_1_1_1_3_r14_nondegenerate", "integration.rubi_1_1_3_5_r24_nondegenerate",
  "integration.rubi_1_1_3_5_r25_nondegenerate", "integration.rubi_1_1_3_5_r26_nondegenerate",
  "integration.rubi_1_1_3_5_r30_nondegenerate", "integration.rubi_1_2_1_2_r43_nondegenerate",
  "integration.rubi_1_2_1_2_r44_nondegenerate", "integration.rubi_1_2_1_2_r45_nondegenerate",
  "integration.rubi_1_2_1_2_r54_nondegenerate",
  "integration.rubi_4_7_9_r1_nondegenerate", "integration.rubi_4_7_9_r2_nondegenerate",
  "integration.rubi_4_7_9_r25_nondegenerate", "integration.rubi_4_7_9_r26_nondegenerate",
  "integration.rubi_4_7_6_r1_nondegenerate", "integration.rubi_4_7_6_r2_nondegenerate",
  "integration.rubi_4_7_6_r16_nondegenerate", "integration.rubi_4_7_6_r17_nondegenerate",
  "integration.rubi_4_1_13_r1_nondegenerate", "integration.rubi_4_1_13_r2_nondegenerate", "integration.rubi_4_1_13_r13_nondegenerate", "integration.rubi_4_1_13_r14_nondegenerate", "integration.rubi_4_1_13_r19_nondegenerate",
  "integration.rubi_4_1_13_r20_nondegenerate", "integration.rubi_4_1_13_r15_nondegenerate", "integration.rubi_4_1_13_r16_nondegenerate", "integration.rubi_4_1_13_r21_nondegenerate", "integration.rubi_4_1_13_r22_nondegenerate",
  "integration.rubi_4_7_9_r11_nondegenerate", "integration.rubi_4_7_9_r12_nondegenerate",
  "integration.rubi_2_3_r32_nondegenerate", "integration.rubi_2_3_r33_nondegenerate",
  "integration.rubi_3_1_4_r17_nondegenerate", "integration.rubi_3_1_5_r16_nondegenerate",
  "integration.rubi_3_1_5_r13_nondegenerate", "integration.rubi_3_1_4_r9_nondegenerate",
  "integration.rubi_3_1_4_r18_nondegenerate", "integration.rubi_3_1_5_r17_nondegenerate",
  "integration.rubi_4_7_9_r16_nondegenerate", "integration.rubi_4_7_9_r27_nondegenerate",
  "integration.rubi_4_7_9_r30_nondegenerate", "integration.rubi_4_1_12_r33_nondegenerate",
  "integration.rubi_4_1_12_r34_nondegenerate",
  "integration.rubi_3_1_1_r3_nondegenerate", "integration.rubi_3_1_2_r5_nondegenerate",
  "integration.rubi_3_1_2_r6_nondegenerate", "integration.rubi_3_1_4_r12_nondegenerate",
  "integration.rubi_3_1_5_r8_nondegenerate", "integration.rubi_3_1_4_r2_nondegenerate",
  "integration.rubi_3_1_5_r3_nondegenerate", "integration.log_power_over_linear_square_nondegenerate",
  "integration.rubi_3_1_3_r1_nondegenerate", "integration.rubi_3_1_3_r10_nondegenerate",
  "integration.rubi_3_1_4_r13_nondegenerate", "integration.rubi_3_1_5_r9_nondegenerate",
  "integration.rubi_3_1_3_r7_nondegenerate", "integration.rubi_4_7_8_r47_nondegenerate",
  "integration.rubi_4_7_8_r48_nondegenerate", "integration.rubi_3_1_2_r3_nondegenerate",
  "integration.rubi_3_1_5_r28_nondegenerate", "integration.rubi_3_5_r16_nondegenerate",
  "integration.rubi_3_5_r21_nondegenerate", "integration.rubi_1_2_3_1_r5_nondegenerate",
  "integration.rubi_2_1_r9_nondegenerate", "integration.rubi_2_1_r10_nondegenerate",
  "integration.rubi_4_1_12_r43_nondegenerate", "integration.rubi_4_1_12_r44_nondegenerate",
  "integration.rubi_4_7_8_r13_nondegenerate", "integration.rubi_4_7_8_r14_nondegenerate",
  "integration.rubi_3_4_r2_nondegenerate", "integration.rubi_3_2_1_r1_nondegenerate",
  "integration.rubi_3_3_r22_nondegenerate", "integration.two_linear_factors_times_powers_nondegenerate",
  "integration.rubi_1_1_1_4_r3_nondegenerate", "integration.rubi_1_2_1_3_r33_nondegenerate",
  "integration.rubi_1_1_3_3_r16_nondegenerate", "integration.rubi_1_1_3_4_r25_nondegenerate",
  "integration.linear_factor_over_linear_nondegenerate", "integration.power_ratio_split_nondegenerate",
  "integration.partial_fractions_general_nondegenerate", "integration.product_over_trinomial_nondegenerate",
  "integration.product_over_quadratic_nondegenerate", "integration.linear_times_two_powers_nondegenerate",
  "integration.linear_times_trinomial_power_nondegenerate", "integration.binomial_ratio_negative_power_nondegenerate",
  "integration.linear_times_quadratic_power_nondegenerate", "integration.linear_sin_trinomial_nondegenerate",
  "integration.linear_cos_trinomial_nondegenerate", "integration.sin_trinomial_square_nondegenerate",
  "integration.cos_trinomial_square_nondegenerate", "integration.log_linear_over_x_nondegenerate",
  "integration.power_log_linear_nondegenerate", "integration.power_sin_log_nondegenerate",
  "integration.power_cos_log_nondegenerate", "integration.sin_x_log_times_log_nondegenerate",
  "integration.cos_x_log_times_log_nondegenerate",
  "integration.rubi_1_1_3_3_r18_nondegenerate", "integration.linear_power_log_linear_nondegenerate",
  "integration.power_log_ratio_nondegenerate", "integration.rubi_3_5_r23_nondegenerate",
  "integration.rubi_3_2_1_r2_nondegenerate", "integration.log_product_power_nondegenerate",
  "integration.power_log_product_nondegenerate", "integration.power_log_product_power_nondegenerate",
  "integration.rubi_1_2_1_2_r5_nondegenerate", "integration.rubi_1_2_3_3_r50_nondegenerate",
  "integration.rubi_4_1_12_r45_nondegenerate", "integration.rubi_4_1_12_r46_nondegenerate",
  "integration.rubi_4_1_12_r53_nondegenerate", "integration.rubi_4_1_12_r54_nondegenerate",
  "integration.rubi_1_2_1_2_r46_nondegenerate",
  "integration.rubi_1_2_1_2_r96_nondegenerate", "integration.rubi_1_2_3_3_r27_nondegenerate",
  "integration.rubi_1_2_3_4_r40_nondegenerate", "integration.rubi_1_2_3_4_r34_nondegenerate",
  "integration.rubi_1_2_3_4_r38_nondegenerate", "integration.rubi_1_2_3_2_r10_nondegenerate",
  "integration.rubi_1_2_3_2_r18_nondegenerate",
  "integration.rubi_1_2_3_4_r64_nondegenerate", "integration.rubi_1_2_3_4_r61_nondegenerate",
  "integration.rubi_3_1_4_r10_nondegenerate", "integration.rubi_3_1_4_r22_nondegenerate",
  "integration.rubi_3_3_r12_nondegenerate", "integration.rubi_3_2_3_r8_nondegenerate",
  "integration.rubi_1_2_1_3_r26_nondegenerate", "integration.rubi_1_1_3_3_r5_nondegenerate",
  "integration.rubi_1_1_3_7_r5_nondegenerate", "integration.log_monomial_log_linear_over_x_nondegenerate",
  "integration.rubi_3_3_r31_nondegenerate", "integration.rubi_3_1_5_r33_nondegenerate",
  "integration.power_two_log_linear_nondegenerate", "integration.log_power_log_binomial_over_x_nondegenerate",
  "integration.power_log_log_nondegenerate", "integration.power_log_monomial_log_linear_nondegenerate",
  "integration.rubi_1_2_2_4_r59_nondegenerate", "integration.rubi_1_2_2_4_r60_nondegenerate",
  "integration.rubi_1_2_2_4_r61_nondegenerate", "integration.rubi_1_2_2_4_r62_nondegenerate",
  "integration.power_log_binomial_nondegenerate", "integration.rubi_1_1_1_3_r53_nondegenerate",
  "integration.rubi_1_3_1_r4_nondegenerate", "integration.rubi_1_3_2_r1_nondegenerate",
  "integration.rubi_2_3_r11_nondegenerate", "integration.rubi_2_3_r23_nondegenerate",
  "integration.rubi_2_3_r24_nondegenerate", "integration.rubi_2_3_r26_nondegenerate",
  "integration.rubi_2_3_r35_nondegenerate",
  "integration.rubi_1_2_3_3_r41", "integration.rubi_1_2_3_3_r42", "integration.rubi_1_2_3_3_r47", "integration.rubi_1_2_3_4_r92", "integration.rubi_1_2_3_4_r93", "integration.rubi_1_2_3_4_r100", "integration.rubi_1_2_1_2_r93", "integration.rubi_1_2_1_2_r94", "integration.rubi_1_2_1_2_r95",
  "integration.rubi_7_3_4_r140", "integration.rubi_5_3_4_r41", "integration.rubi_7_3_4_r41", "integration.rubi_7_3_4_r138", "integration.rubi_5_3_4_r140", "integration.rubi_7_3_4_r132", "integration.rubi_5_3_4_r138", "integration.rubi_5_3_4_r132", "integration.rubi_7_3_1_r160", "integration.rubi_7_3_1_r61", "integration.rubi_7_3_1_r158", "integration.rubi_7_3_1_r152", "integration.rubi_5_3_4_r107", "integration.rubi_6_7_7_r33",
  "integration.rubi_7_3_4_misc_r1", "integration.rubi_7_3_7_r1", "integration.rubi_7_3_1_r168", "integration.rubi_5_3_7_r1", "integration.rubi_7_3_4_r134", "integration.rubi_7_3_1_r154", "integration.rubi_5_3_4_r134", "integration.rubi_7_3_4_r142", "integration.rubi_7_3_1_r162", "integration.rubi_5_3_4_r142",
  "integration.rubi_5_3_7_r43", "integration.rubi_5_3_7_r45", "integration.rubi_7_3_4_misc_r13", "integration.rubi_7_3_7_r13", "integration.rubi_5_3_7_r13",
  "integration.rubi_7_3_4_r89", "integration.rubi_7_3_1_r109", "integration.rubi_5_3_4_r89", "integration.rubi_7_3_4_r91", "integration.rubi_7_3_1_r111", "integration.rubi_5_3_4_r91",
  "integration.rubi_7_3_4_r39", "integration.rubi_7_3_1_r59",
  "integration.rubi_7_3_4_r107", "integration.rubi_7_3_1_r127", "integration.rubi_7_3_4_r130", "integration.rubi_7_3_1_r150", "integration.rubi_7_3_7_r3", "integration.rubi_7_3_4_misc_r3", "integration.rubi_6_1_12_r19", "integration.rubi_6_1_12_r20",
  "integration.rubi_7_3_4_r5", "integration.rubi_7_3_1_r25", "integration.rubi_5_3_4_r5", "integration.rubi_7_3_4_r95", "integration.rubi_7_3_1_r115", "integration.rubi_5_3_4_r95",
  "integration.rubi_7_2_3_r1", "integration.rubi_7_2_4_r1", "integration.rubi_6_7_9_r70", "integration.rubi_6_1_11_r7", "integration.rubi_6_1_11_r8", "integration.rubi_6_1_11_r19", "integration.rubi_6_1_11_r20", "integration.rubi_7_3_4_r136", "integration.rubi_7_3_1_r156", "integration.rubi_4_7_9_r72", "integration.rubi_4_7_9_r73", "integration.rubi_4_7_9_r74", "integration.rubi_4_7_9_r75", "integration.rubi_4_7_9_r17", "integration.rubi_4_7_9_r18", "integration.rubi_4_7_9_r19", "integration.rubi_4_7_9_r20", "integration.rubi_6_7_9_r8", "integration.rubi_6_7_9_r16", "integration.rubi_6_7_9_r17", "integration.rubi_6_7_9_r18", "integration.rubi_4_7_6_r10", "integration.rubi_4_7_6_r11", "integration.rubi_4_7_6_r12", "integration.rubi_4_7_6_r13", "integration.rubi_6_7_6_r5", "integration.rubi_6_7_6_r10", "integration.rubi_6_7_6_r11", "integration.rubi_6_7_6_r12", "integration.rubi_6_7_6_r13", "integration.rubi_7_3_4_misc_r7", "integration.rubi_7_3_4_misc_r9", "integration.rubi_7_3_7_r7", "integration.rubi_7_3_7_r9", "integration.rubi_5_3_7_r23", "integration.rubi_7_3_4_misc_r23", "integration.rubi_7_3_7_r23", "integration.rubi_6_7_7_r24", "integration.rubi_6_7_7_r25", "integration.rubi_6_7_7_r30", "integration.rubi_5_1_1_r1", "integration.rubi_5_1_1_r2", "integration.rubi_7_1_1_r1", "integration.rubi_7_2_1_r1", "integration.rubi_5_1_2_r5", "integration.rubi_5_1_2_r6", "integration.rubi_7_1_2_r3", "integration.rubi_7_2_2_r3",
  "integration.rubi_6_7_9_r86", "integration.rubi_6_7_9_r87", "integration.rubi_6_7_9_r88", "integration.rubi_6_7_9_r89", "integration.rubi_4_7_9_r96", "integration.rubi_4_7_9_r97", "integration.rubi_6_7_7_r1", "integration.rubi_6_7_7_r2", "integration.rubi_6_7_7_r3", "integration.rubi_6_7_7_r4", "integration.rubi_6_7_7_r7", "integration.rubi_4_7_7_r13", "integration.rubi_4_7_7_r14", "integration.rubi_4_7_7_r17", "integration.rubi_4_7_7_r18", "integration.rubi_6_7_8_r3", "integration.rubi_6_7_8_r4", "integration.rubi_6_7_8_r5", "integration.rubi_6_7_8_r6",
  "integration.rubi_7_3_1_r1", "integration.rubi_7_3_4_misc_r41", "integration.rubi_7_3_7_r41", "integration.rubi_6_7_9_r73", "integration.rubi_6_7_9_r75",
  "integration.rubi_1_2_2_3_r25",
  "integration.rubi_6_1_12_r27", "integration.rubi_6_1_12_r28", "integration.rubi_4_1_12_r41", "integration.rubi_4_1_12_r42", "integration.rubi_3_3_r9",
  "integration.rubi_1_3_3_r24", "integration.rubi_6_7_9_r76",
  "integration.rubi_6_1_12_r1", "integration.rubi_6_1_12_r2", "integration.rubi_6_1_12_r29", "integration.rubi_6_1_12_r30", "integration.rubi_6_1_12_r55", "integration.rubi_6_1_12_r56", "integration.rubi_6_1_12_r7", "integration.rubi_6_1_12_r8", "integration.rubi_6_1_13_r1", "integration.rubi_6_1_13_r2", "integration.rubi_6_7_9_r91", "integration.rubi_6_7_9_r92", "integration.rubi_6_7_9_r93", "integration.rubi_6_7_9_r94",
  "integration.rubi_4_1_2_1_r14", "integration.rubi_4_3_2_1_r29", "integration.rubi_4_3_4_1_r9", "integration.rubi_4_5_2_1_r13", "integration.rubi_4_5_2_1_r19", "integration.rubi_7_3_1_r159", "integration.rubi_7_3_1_r161", "integration.rubi_7_3_1_r62", "integration.rubi_7_3_4_r139", "integration.rubi_7_3_4_r141", "integration.rubi_7_3_4_r42",
  "integration.rubi_5_3_4_r42", "integration.rubi_5_3_4_r139", "integration.rubi_5_3_4_r141", "integration.rubi_4_5_3_1_r10", "integration.rubi_4_5_1_2_r51", "integration.rubi_4_5_4_1_r18", "integration.rubi_4_5_4_1_r19", "integration.rubi_4_5_2_1_r12", "integration.rubi_4_5_1_1_r7", "integration.rubi_4_3_1_1_r12", "integration.rubi_4_3_4_1_r8",
  "integration.rubi_4_5_2_1_r11", "integration.rubi_4_1_3_1_r36", "integration.rubi_4_1_5_r27", "integration.rubi_4_1_5_r28", "integration.rubi_4_3_3_1_r24", "integration.rubi_4_3_4_1_r7", "integration.rubi_4_3_4_1_r10", "integration.rubi_4_3_4_1_r11", "integration.rubi_4_3_2_1_r10", "integration.rubi_4_3_2_1_r49", "integration.rubi_4_3_4_2_r20", "integration.rubi_4_3_4_2_r21", "integration.rubi_6_7_9_r45", "integration.rubi_6_7_9_r48",
  "integration.rubi_3_1_2_r2_nondegenerate", "integration.rubi_3_1_2_r7_nondegenerate",
  "integration.rubi_1_1_1_2_r21",
  "integration.rubi_4_1_1_1_r6_nondegenerate", "integration.rubi_4_5_1_1_r4_nondegenerate", "integration.rubi_4_1_1_1_r2_nondegenerate", "integration.rubi_6_1_13_r7_nondegenerate", "integration.rubi_6_1_13_r8_nondegenerate", "integration.rubi_4_3_2_1_r3_nondegenerate", "integration.rubi_4_1_1_1_r11_nondegenerate", "integration.rubi_4_1_2_1_r1_nondegenerate", "integration.rubi_4_1_7_r1_nondegenerate", "integration.rubi_5_3_6_r13_nondegenerate", "integration.rubi_5_3_6_r55_nondegenerate", "integration.rubi_5_3_4_r15_nondegenerate", "integration.rubi_5_3_4_r16_nondegenerate",
  "integration.rubi_7_3_1_r35_nondegenerate", "integration.rubi_7_3_4_r15_nondegenerate", "integration.rubi_7_3_1_r36_nondegenerate", "integration.rubi_7_3_4_r16_nondegenerate", "integration.rubi_4_1_4_1_r2_nondegenerate",
  "integration.rubi_7_3_1_r17_nondegenerate", "integration.rubi_7_3_3_r9_nondegenerate", "integration.rubi_7_3_1_r123_nondegenerate", "integration.rubi_7_3_4_r103_nondegenerate", "integration.rubi_7_3_1_r124_nondegenerate", "integration.rubi_7_3_4_r104_nondegenerate", "integration.rubi_7_3_1_r18_nondegenerate", "integration.rubi_7_3_3_r10_nondegenerate", "integration.rubi_7_3_1_r29_nondegenerate", "integration.rubi_7_3_4_r9_nondegenerate", "integration.rubi_7_3_1_r47_nondegenerate", "integration.rubi_7_3_4_r27_nondegenerate", "integration.rubi_7_3_1_r69_nondegenerate", "integration.rubi_7_3_1_r73_nondegenerate", "integration.rubi_7_3_1_r79_nondegenerate", "integration.rubi_7_3_4_r49_nondegenerate", "integration.rubi_7_3_4_r53_nondegenerate", "integration.rubi_7_3_4_r59_nondegenerate",
  "integration.rubi_7_3_1_r70_nondegenerate", "integration.rubi_7_3_1_r74_nondegenerate", "integration.rubi_7_3_1_r80_nondegenerate", "integration.rubi_7_3_4_r50_nondegenerate", "integration.rubi_7_3_4_r54_nondegenerate", "integration.rubi_7_3_4_r60_nondegenerate",
  "integration.rubi_7_3_1_r65_nondegenerate", "integration.rubi_7_3_4_r45_nondegenerate", "integration.rubi_7_3_1_r67_nondegenerate", "integration.rubi_7_3_4_r47_nondegenerate", "integration.rubi_7_3_1_r66_nondegenerate", "integration.rubi_7_3_4_r46_nondegenerate", "integration.rubi_7_3_1_r68_nondegenerate", "integration.rubi_7_3_4_r48_nondegenerate",
  "integration.rubi_7_3_1_r85_nondegenerate", "integration.rubi_7_3_4_r65_nondegenerate", "integration.rubi_7_3_1_r86_nondegenerate", "integration.rubi_7_3_4_r66_nondegenerate",
  "integration.rubi_7_3_1_r43_nondegenerate", "integration.rubi_7_3_4_r23_nondegenerate", "integration.rubi_7_3_1_r44_nondegenerate", "integration.rubi_7_3_4_r24_nondegenerate",
  "integration.rubi_7_3_1_r83_nondegenerate", "integration.rubi_7_3_4_r63_nondegenerate",
  "integration.rubi_7_3_1_r87_nondegenerate", "integration.rubi_7_3_4_r67_nondegenerate",
  "integration.rubi_7_3_1_r94_nondegenerate", "integration.rubi_7_3_4_r74_nondegenerate",
  "integration.rubi_7_3_1_r101_nondegenerate", "integration.rubi_7_3_4_r81_nondegenerate",
  "integration.rubi_7_3_1_r89_nondegenerate", "integration.rubi_7_3_4_r69_nondegenerate",
  "integration.rubi_7_3_1_r118_nondegenerate", "integration.rubi_7_3_4_r98_nondegenerate",
  "integration.rubi_7_3_1_r82_nondegenerate", "integration.rubi_7_3_4_r62_nondegenerate",
  "integration.rubi_7_3_1_r136_nondegenerate", "integration.rubi_7_3_4_r116_nondegenerate",
  "integration.rubi_7_3_1_r21_nondegenerate", "integration.rubi_7_3_4_r1_nondegenerate",
  "integration.rubi_7_3_1_r172_nondegenerate", "integration.rubi_7_3_2_r5_nondegenerate", "integration.rubi_7_3_1_r173_nondegenerate", "integration.rubi_7_3_2_r6_nondegenerate",
  "integration.rubi_7_3_2_r1_nondegenerate", "integration.rubi_7_3_5_r1_nondegenerate", "integration.rubi_7_3_2_r2_nondegenerate", "integration.rubi_7_3_5_r2_nondegenerate", "integration.rubi_7_3_5_r5_nondegenerate", "integration.rubi_7_3_2_r5_b_nondegenerate", "integration.rubi_7_3_2_r9_nondegenerate", "integration.rubi_7_3_5_r9_nondegenerate", "integration.rubi_7_3_2_r10_nondegenerate", "integration.rubi_7_3_5_r10_nondegenerate", "integration.rubi_7_3_1_pow_r5_nondegenerate", "integration.rubi_7_3_2_r13_nondegenerate",
  "integration.rubi_7_3_7_r21_nondegenerate", "integration.rubi_7_3_4_misc_r21_nondegenerate", "integration.rubi_7_3_7_r17_nondegenerate", "integration.rubi_7_3_4_misc_r17_nondegenerate",
  "integration.rubi_7_3_7_r45_nondegenerate", "integration.rubi_7_3_4_misc_r45_nondegenerate",
  "integration.rubi_7_3_1_r39_nondegenerate", "integration.rubi_7_3_4_r19_nondegenerate",
  "integration.rubi_7_3_7_r33_nondegenerate", "integration.rubi_7_3_4_misc_r33_nondegenerate", "integration.rubi_7_3_7_r34_nondegenerate", "integration.rubi_7_3_4_misc_r34_nondegenerate",
  "integration.rubi_7_3_1_r7_nondegenerate", "integration.rubi_7_3_1_r8_nondegenerate", "integration.rubi_7_3_2_r7_nondegenerate", "integration.rubi_7_3_5_r7_nondegenerate", "integration.rubi_7_3_2_r8_nondegenerate", "integration.rubi_7_3_5_r8_nondegenerate", "integration.rubi_7_3_1_r9_nondegenerate", "integration.rubi_7_3_3_r1_nondegenerate", "integration.rubi_7_3_5_r6_nondegenerate", "integration.rubi_7_3_2_r6_b_nondegenerate",
  "integration.rubi_7_3_1_r31_nondegenerate", "integration.rubi_7_3_4_r11_nondegenerate", "integration.rubi_7_3_1_r51_nondegenerate", "integration.rubi_7_3_4_r31_nondegenerate",
  "integration.rubi_7_3_7_r37_nondegenerate", "integration.rubi_7_3_4_misc_r37_nondegenerate", "integration.rubi_7_3_7_r38_nondegenerate", "integration.rubi_7_3_4_misc_r38_nondegenerate", "integration.rubi_7_3_7_r39_nondegenerate", "integration.rubi_7_3_4_misc_r39_nondegenerate", "integration.rubi_7_3_7_r40_nondegenerate", "integration.rubi_7_3_4_misc_r40_nondegenerate",
  "integration.rubi_7_3_1_r164_nondegenerate", "integration.rubi_7_3_4_r144_nondegenerate",
  "integration.rubi_7_1_6_r1_nondegenerate", "integration.rubi_7_1_1_r2_nondegenerate", "integration.rubi_7_1_1_r3_nondegenerate", "integration.rubi_7_1_3_r7_nondegenerate", "integration.rubi_7_1_4_r1_nondegenerate", "integration.rubi_7_1_2_r6_nondegenerate", "integration.rubi_7_1_2_r2_nondegenerate", "integration.rubi_7_1_5_r2_nondegenerate",
  "integration.rubi_7_1_3_r2_nondegenerate", "integration.rubi_7_1_4_r23_nondegenerate", "integration.rubi_7_1_5_r11_nondegenerate",
  "integration.rubi_7_1_6_r2_nondegenerate",
  "integration.rubi_7_2_2_r2_nondegenerate", "integration.rubi_7_2_5_r2_nondegenerate", "integration.rubi_7_2_6_r1_nondegenerate", "integration.rubi_7_2_1_r2_nondegenerate", "integration.rubi_7_2_1_r3_nondegenerate", "integration.rubi_7_2_2_r6_nondegenerate", "integration.rubi_7_2_2_r1_nondegenerate",
  "integration.rubi_7_2_6_r2_nondegenerate", "integration.rubi_7_2_3_r4_nondegenerate", "integration.rubi_7_2_3_r5_nondegenerate",
  "integration.rubi_4_1_2_1_r15_nondegenerate", "integration.rubi_4_1_4_1_r1_nondegenerate", "integration.rubi_4_3_1_1_r5_nondegenerate", "integration.rubi_4_5_7_r6_nondegenerate", "integration.rubi_4_5_1_1_r17_nondegenerate", "integration.rubi_4_5_1_2_r45_nondegenerate", "integration.rubi_4_5_1_2_r1_nondegenerate", "integration.rubi_4_3_4_1_r1_nondegenerate", "integration.rubi_4_3_4_1_r2_nondegenerate",
  "integration.rubi_4_1_10_r1_nondegenerate", "integration.rubi_4_1_7_r3_nondegenerate", "integration.rubi_4_3_1_1_r1_nondegenerate", "integration.rubi_4_7_9_r47_nondegenerate", "integration.rubi_4_7_9_r48_nondegenerate",
  "integration.rubi_4_5_1_2_r3_nondegenerate", "integration.rubi_4_5_1_2_r4_nondegenerate", "integration.rubi_4_5_10_r5_nondegenerate",
  "integration.rubi_5_3_1_r5_nondegenerate", "integration.rubi_5_3_2_r13_nondegenerate", "integration.rubi_4_1_2_1_r56_nondegenerate", "integration.rubi_4_1_4_1_r7_nondegenerate", "integration.rubi_4_3_4_1_r4_nondegenerate", "integration.rubi_4_5_4_1_r7_nondegenerate", "integration.rubi_4_5_1_2_r2_nondegenerate",
  "integration.rubi_4_1_9_r1_nondegenerate", "integration.rubi_4_1_9_r2_nondegenerate", "integration.rubi_4_3_9_r1_nondegenerate", "integration.rubi_4_3_9_r2_nondegenerate", "integration.rubi_4_5_9_r1_nondegenerate", "integration.rubi_4_5_9_r2_nondegenerate",
  "integration.rubi_4_1_2_2_r6_nondegenerate", "integration.rubi_4_5_4_1_r10_nondegenerate", "integration.rubi_4_5_3_1_r3_nondegenerate", "integration.rubi_4_5_1_2_r52_nondegenerate", "integration.rubi_4_1_7_r4_nondegenerate",
  "integration.rubi_4_1_9_r29_nondegenerate", "integration.rubi_4_1_9_r30_nondegenerate", "integration.rubi_4_3_9_r19_nondegenerate", "integration.rubi_4_3_9_r20_nondegenerate", "integration.rubi_4_5_9_r11_nondegenerate", "integration.rubi_4_5_9_r12_nondegenerate", "integration.rubi_4_1_9_r5_nondegenerate", "integration.rubi_4_1_9_r6_nondegenerate", "integration.rubi_4_3_9_r9_nondegenerate", "integration.rubi_4_3_9_r10_nondegenerate", "integration.rubi_4_3_9_r15_nondegenerate", "integration.rubi_4_3_9_r16_nondegenerate", "integration.rubi_4_5_9_r5_nondegenerate", "integration.rubi_4_5_9_r6_nondegenerate",
  "integration.rubi_4_1_2_1_r23_nondegenerate",
  "integration.rubi_4_7_4_r6_nondegenerate", "integration.rubi_4_7_4_r7_nondegenerate", "integration.rubi_4_7_4_r31_nondegenerate",
  "integration.rubi_4_1_4_1_r6_nondegenerate", "integration.rubi_4_3_4_1_r3_nondegenerate", "integration.rubi_4_5_4_1_r1_nondegenerate", "integration.rubi_4_1_2_2_r35_nondegenerate", "integration.rubi_4_1_5_r32_nondegenerate", "integration.rubi_4_1_5_r31_nondegenerate", "integration.rubi_4_1_10_r8_nondegenerate",
  "integration.rubi_4_1_2_2_r47_nondegenerate", "integration.rubi_4_1_2_2_r83_nondegenerate",
  "integration.rubi_4_7_9_r21_nondegenerate", "integration.rubi_4_7_9_r22_nondegenerate", "integration.rubi_6_7_9_r19_nondegenerate", "integration.rubi_6_7_9_r20_nondegenerate", "integration.rubi_6_7_9_r1_nondegenerate", "integration.rubi_6_7_9_r2_nondegenerate", "integration.rubi_4_7_9_r15_nondegenerate", "integration.rubi_6_7_9_r14_nondegenerate", "integration.rubi_6_7_9_r13_nondegenerate", "integration.rubi_4_7_9_r13_nondegenerate", "integration.rubi_4_7_9_r14_nondegenerate", "integration.rubi_6_7_9_r11_nondegenerate", "integration.rubi_6_7_9_r12_nondegenerate",
  "integration.rubi_1_1_3_5_r12_nondegenerate", "integration.rubi_1_2_1_7_r29_nondegenerate", "integration.rubi_1_2_1_7_r30_nondegenerate", "integration.rubi_1_2_1_7_r31_nondegenerate", "integration.rubi_1_2_1_7_r32_nondegenerate", "integration.rubi_1_1_1_4_r16_nondegenerate", "integration.rubi_1_1_3_5_r27_nondegenerate",
  "integration.rubi_4_7_9_r28_nondegenerate", "integration.rubi_4_7_9_r29_nondegenerate", "integration.rubi_4_7_9_r31_nondegenerate", "integration.rubi_4_7_9_r32_nondegenerate", "integration.rubi_6_7_9_r23_nondegenerate", "integration.rubi_6_7_9_r24_nondegenerate", "integration.rubi_6_7_9_r25_nondegenerate", "integration.rubi_6_7_9_r26_nondegenerate", "integration.rubi_6_7_9_r27_nondegenerate", "integration.rubi_6_7_9_r28_nondegenerate", "integration.rubi_6_7_9_r29_nondegenerate", "integration.rubi_6_7_9_r30_nondegenerate", "integration.rubi_6_7_9_r31_nondegenerate", "integration.rubi_6_7_9_r32_nondegenerate", "integration.rubi_6_7_9_r33_nondegenerate", "integration.rubi_6_7_9_r34_nondegenerate",
  "integration.rubi_6_7_9_r9_nondegenerate", "integration.rubi_6_7_9_r10_nondegenerate", "integration.rubi_6_7_9_r4_nondegenerate", "integration.rubi_4_3_2_1_r4_nondegenerate", "integration.rubi_4_1_2_1_r2_nondegenerate", "integration.rubi_4_3_3_1_r2_nondegenerate", "integration.rubi_4_3_2_1_r19_nondegenerate", "integration.rubi_4_1_2_1_r13_nondegenerate", "integration.rubi_6_1_13_r9_nondegenerate", "integration.rubi_6_1_13_r10_nondegenerate", "integration.rubi_4_5_2_1_r17_nondegenerate", "integration.rubi_4_7_9_r76_nondegenerate", "integration.rubi_4_7_9_r77_nondegenerate", "integration.rubi_6_7_9_r78_nondegenerate", "integration.rubi_6_7_9_r79_nondegenerate", "integration.rubi_4_5_4_1_r8_nondegenerate", "integration.rubi_4_5_4_1_r9_nondegenerate", "integration.rubi_6_7_8_r47_nondegenerate", "integration.rubi_6_7_8_r48_nondegenerate", "integration.rubi_6_3_12_r3_nondegenerate",
  "integration.rubi_4_3_3_1_r19_nondegenerate", "integration.rubi_4_3_10_r17_nondegenerate",
  "integration.rubi_4_1_4_2_r2_nondegenerate", "integration.rubi_4_1_4_2_r1_nondegenerate", "integration.rubi_4_3_4_2_r2_nondegenerate", "integration.rubi_4_3_4_2_r1_nondegenerate", "integration.rubi_4_5_4_1_r2_nondegenerate", "integration.rubi_4_5_4_2_r2_nondegenerate", "integration.rubi_4_5_4_2_r1_nondegenerate",
  "integration.rubi_4_1_3_1_r21_nondegenerate", "integration.rubi_4_1_3_1_r37_nondegenerate", "integration.rubi_4_1_4_2_r36_nondegenerate", "integration.rubi_4_1_4_2_r35_nondegenerate", "integration.rubi_4_1_2_1_r89_nondegenerate", "integration.rubi_4_5_3_1_r12_nondegenerate", "integration.rubi_4_5_3_1_r43_nondegenerate", "integration.rubi_1_1_3_5_r31_nondegenerate", "integration.rubi_1_2_1_2_r2_nondegenerate", "integration.rubi_1_2_1_3_r21_nondegenerate", "integration.rubi_1_2_1_4_r4_nondegenerate", "integration.rubi_1_2_1_3_r37_nondegenerate", "integration.rubi_1_2_3_4_r18_nondegenerate", "integration.rubi_1_2_3_3_r51_nondegenerate", "integration.rubi_1_2_3_3_r11_nondegenerate", "integration.rubi_4_1_2_2_r78_nondegenerate", "integration.rubi_4_1_2_2_r48_nondegenerate", "integration.rubi_4_1_5_r37_nondegenerate", "integration.rubi_4_1_5_r38_nondegenerate",
  "integration.rubi_4_1_2_1_r26_nondegenerate", "integration.rubi_4_1_2_1_r28_nondegenerate", "integration.rubi_4_1_2_1_r57_nondegenerate", "integration.rubi_4_1_2_1_r58_nondegenerate",
  "integration.rubi_4_1_2_1_r17_nondegenerate", "integration.rubi_4_1_2_1_r25_nondegenerate", "integration.rubi_4_1_2_1_r27_nondegenerate",
  "integration.rubi_4_1_4_1_r3_nondegenerate", "integration.rubi_4_1_4_1_r5_nondegenerate", "integration.rubi_4_1_4_1_r12_nondegenerate", "integration.rubi_4_1_4_1_r13_nondegenerate", "integration.rubi_4_1_4_1_r14_nondegenerate", "integration.rubi_4_1_4_1_r15_nondegenerate", "integration.rubi_4_1_4_1_r10_nondegenerate", "integration.rubi_4_1_4_1_r11_nondegenerate", "integration.rubi_4_1_4_2_r3_nondegenerate", "integration.rubi_4_1_4_2_r4_nondegenerate", "integration.rubi_4_3_2_1_r7_nondegenerate", "integration.rubi_4_3_2_1_r8_nondegenerate", "integration.rubi_4_3_2_1_r20_nondegenerate", "integration.rubi_4_3_2_1_r21_nondegenerate", "integration.rubi_4_3_3_1_r4_nondegenerate", "integration.rubi_4_3_3_1_r5_nondegenerate", "integration.rubi_4_3_4_1_r12_nondegenerate", "integration.rubi_4_3_4_1_r13_nondegenerate", "integration.rubi_4_3_4_1_r14_nondegenerate", "integration.rubi_4_3_4_1_r15_nondegenerate", "integration.rubi_4_3_4_2_r4_nondegenerate", "integration.rubi_4_3_4_2_r6_nondegenerate", "integration.rubi_4_3_4_2_r7_nondegenerate", "integration.rubi_4_3_1_1_r10_nondegenerate",
  "integration.rubi_4_5_4_1_r14_nondegenerate", "integration.rubi_4_5_4_1_r15_nondegenerate", "integration.rubi_4_5_1_2_r50_nondegenerate", "integration.rubi_4_5_3_1_r14_nondegenerate", "integration.rubi_4_5_3_1_r15_nondegenerate", "integration.rubi_4_5_3_1_r8_nondegenerate", "integration.rubi_4_5_4_1_r6_nondegenerate", "integration.rubi_4_5_4_2_r10_nondegenerate", "integration.rubi_4_5_4_2_r11_nondegenerate", "integration.rubi_4_5_4_2_r12_nondegenerate", "integration.rubi_4_5_4_2_r19_nondegenerate", "integration.rubi_4_5_4_2_r20_nondegenerate", "integration.rubi_4_5_4_2_r21_nondegenerate", "integration.rubi_4_5_4_2_r22_nondegenerate", "integration.rubi_4_5_4_2_r9_nondegenerate", "integration.rubi_4_5_3_1_r2_nondegenerate", "integration.rubi_4_5_4_2_r5_nondegenerate", "integration.rubi_4_5_4_2_r6_nondegenerate",
  "integration.rubi_4_1_10_r2_nondegenerate", "integration.rubi_4_1_2_2_r26_nondegenerate", "integration.rubi_4_1_4_2_r5_nondegenerate", "integration.rubi_4_1_4_2_r6_nondegenerate", "integration.rubi_4_1_3_1_r23_nondegenerate", "integration.rubi_4_1_5_r6_nondegenerate", "integration.rubi_4_1_6_r14_nondegenerate", "integration.rubi_4_1_6_r27_nondegenerate", "integration.rubi_4_1_6_r28_nondegenerate", "integration.rubi_4_1_6_r29_nondegenerate", "integration.rubi_4_1_6_r41_nondegenerate", "integration.rubi_4_1_6_r42_nondegenerate", "integration.rubi_4_1_6_r43_nondegenerate", "integration.rubi_4_1_1_2_r3_x_nondegenerate", "integration.rubi_4_1_7_r14_nondegenerate", "integration.rubi_4_1_7_r5_nondegenerate", "integration.rubi_4_1_6_r30_nondegenerate",
  "integration.rubi_5_3_3_r9_nondegenerate", "integration.rubi_5_3_4_r103_nondegenerate",
  "integration.rubi_1_2_1_3_r34_nondegenerate", "integration.rubi_4_1_6_r24_nondegenerate", "integration.rubi_4_1_6_r25_nondegenerate", "integration.rubi_4_1_6_r26_nondegenerate", "integration.rubi_4_1_0_1_r1_nondegenerate", "integration.rubi_4_1_2_2_r34_nondegenerate", "integration.rubi_4_1_2_2_r39_nondegenerate", "integration.rubi_1_2_1_3_r27_nondegenerate", "integration.rubi_1_2_1_3_r59_nondegenerate", "integration.rubi_1_2_1_3_r6_nondegenerate", "integration.rubi_4_5_4_2_r15_nondegenerate", "integration.rubi_4_5_4_2_r16_nondegenerate", "integration.rubi_4_5_1_2_r26_nondegenerate", "integration.rubi_4_7_6_r19_nondegenerate", "integration.rubi_4_7_6_r21_nondegenerate", "integration.rubi_4_7_6_r9_nondegenerate",
  "integration.source_1_4_3_r31"]

-- A conditional rule applies only when its conditions are decided: int(λt. t^m)
-- stays (m ≠ -1 is undecided), int(λt. t^(-1)) stays (decided false),
-- int(λt. t^3) rewrites with the power rule (3 ≠ -1 decided true).
#guard (rewrite rules (.integral "t" (.pow t (.var "m")))).isNone
#guard (rewrite rules (.integral "t" (.pow t (.int (-1))))).isNone
#guard (rewrite rules (.integral "t" (.pow t (.int 3)))).map (·.2) ==
  some (.lam "t" (.app2 .mul (.pow t (.app2 .add (.int 3) (.int 1)))
    (.pow (.app2 .add (.int 3) (.int 1)) (.int (-1)))))
#guard (rewrite rules (.integral "t" (.pow t (.int 3)))).map (·.1) == some "integration.power"

-- int(λt. u) ⟶ λt. u t: the input's bound variable is kept.
#guard (rewrite rules (.integral "t" (.var "u"))).map (·.2) ==
  some (.lam "t" (.app2 .mul (.var "u") t))

-- FreeQ as an independence constraint: int(λt. t) is not a constant.
#guard (rewrite rules (.integral "t" t)).isNone

-- int(λt. ln(c t^n)) ⟶ λt. t ln(c t^n) - n t.
#guard (rewrite rules (.integral "t" (.app1 .ln (.app2 .mul (.var "c") (.pow t (.var "n")))))).map
    (·.2) ==
  some (.lam "t" (.app2 .add
    (.app2 .mul t (.app1 .ln (.app2 .mul (.var "c") (.pow t (.var "n")))))
    (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) t)))

-- Refuted rules are not applied: int(λt. 1 · t^(-1)) stays.
#guard (rewrite rules (.integral "t" (.app2 .mul (.int 1) (.pow t (.int (-1)))))).isNone

-- Antiderivative rules do not apply to derivatives, and vice versa.
#guard (rewrite rules (.diff "t" (.var "u"))).isNone
#guard (rewrite (Calculus.catalog.map (·.rule)) (.integral "t" (.var "u"))).isNone

-- Unconditional, non-recursive rules apply once: their results are lambdas.
#guard (rules.filter fun r => r.conditions.isEmpty && r.shape == .antideriv).all fun r =>
  match rewrite rules (.integral r.x r.body) with
  | some (_, out) => (rewrite rules out).isNone
  | none => false

-- Proofs and counterexamples use the standard axioms only.
run_meta do
  for e in Integration.catalog do
    for (_, thm) in e.proofs ++ e.counterexamples do
      let forbidden := (← Lean.collectAxioms thm).toList.filter fun ax =>
        ax ∉ [``propext, ``Classical.choice, ``Quot.sound]
      unless forbidden.isEmpty do
        throwError "{thm} depends on {forbidden}"

end OSRTest.Integration
