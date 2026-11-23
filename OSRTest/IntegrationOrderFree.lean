import OSR.IntegrationRec204
import OSR.IntegrationRec205
import OSR.IntegrationRec206
import OSR.Semantics

/-! Tests for the order-free variant of RUBI 1.1.3.4 #28. -/

open OSR OSR.Calculus OSR.IntegrationRec205

open OSR.IntegrationRec204

#check rubi1134r27OrderFree_real
#check rubi1134r27OrderFree_complex
#check rubi1134r27OriginalConditions_imply_OrderFree

#guard rubi1134r27OrderFree.id == "integration.rubi_1_1_3_4_r27_order_free"
#guard rubi1134r27OrderFree.body == OSR.IntegrationNum1.rubi1134r27Nondeg.body
#guard rubi1134r27OrderFree.result == OSR.IntegrationNum1.rubi1134r27Nondeg.result
#guard rubi1134r27OrderFree.integrals == OSR.IntegrationNum1.rubi1134r27Nondeg.integrals
#guard rubi1134r27OrderFree.independent == OSR.IntegrationNum1.rubi1134r27Nondeg.independent
#guard rubi1134r27OrderFree.legacyId == OSR.IntegrationNum1.rubi1134r27Nondeg.legacyId
#guard OSR.IntegrationNum1.rubi1134r27Nondeg.conditions.contains rubi1134r27Denominator
#guard rubi1134r27OrderFree.conditions.length == 1
#guard !(rubi1134r27OrderFree.symbols.contains ⟨"relation1", "gt"⟩)
#guard (OSR.Registry.mappingAssurance rubi1134r27OrderFree.symbols .complex).certifiable

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

open OSR.IntegrationRec206

#check rubi1134r29OrderFree_real
#check rubi1134r29OrderFree_complex
#check rubi1134r29OriginalConditions_imply_OrderFree

#guard rubi1134r29OrderFree.id == "integration.rubi_1_1_3_4_r29_order_free"
#guard rubi1134r29OrderFree.body == OSR.IntegrationNum1.rubi1134r29Nondeg.body
#guard rubi1134r29OrderFree.result == OSR.IntegrationNum1.rubi1134r29Nondeg.result
#guard rubi1134r29OrderFree.integrals == OSR.IntegrationNum1.rubi1134r29Nondeg.integrals
#guard rubi1134r29OrderFree.independent == OSR.IntegrationNum1.rubi1134r29Nondeg.independent
#guard rubi1134r29OrderFree.legacyId == OSR.IntegrationNum1.rubi1134r29Nondeg.legacyId
#guard !(rubi1134r29OrderFree.symbols.contains ⟨"relation1", "gt"⟩)
#guard (OSR.Registry.mappingAssurance rubi1134r29OrderFree.symbols .complex).certifiable
