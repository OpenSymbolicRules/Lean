import OSR.IntegrationRec205
import OSR.Semantics

/-! Tests for the order-free variant of RUBI 1.1.3.4 #28. -/

open OSR OSR.Calculus OSR.IntegrationRec205

#check rubi1134r28OrderFree_real
#check rubi1134r28OrderFree_complex
#check rubi1134r28OriginalConditions_imply_OrderFree

#guard rubi1134r28OrderFree.id == "integration.rubi_1_1_3_4_r28_order_free"
#guard rubi1134r28OrderFree.body == OSR.IntegrationNum1.rubi1134r28Nondeg.body
#guard rubi1134r28OrderFree.result == OSR.IntegrationNum1.rubi1134r28Nondeg.result
#guard rubi1134r28OrderFree.integrals == OSR.IntegrationNum1.rubi1134r28Nondeg.integrals
#guard rubi1134r28OrderFree.independent == OSR.IntegrationNum1.rubi1134r28Nondeg.independent
#guard rubi1134r28OrderFree.legacyId == OSR.IntegrationNum1.rubi1134r28Nondeg.legacyId
#guard OSR.IntegrationNum1.rubi1134r28Nondeg.conditions.contains rubi1134r28Denominator
#guard rubi1134r28OrderFree.conditions.length == 1
#guard !(rubi1134r28OrderFree.symbols.contains ⟨"relation1", "gt"⟩)
#guard (OSR.Registry.mappingAssurance rubi1134r28OrderFree.symbols .complex).certifiable
#guard !(OSR.Registry.mappingAssurance OSR.IntegrationNum1.rubi1134r28Nondeg.symbols .complex).certifiable
