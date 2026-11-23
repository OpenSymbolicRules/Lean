import OSR.IntegrationRec207
import OSR.IntegrationRec208
import OSR.IntegrationRec209

/-! Proof promotion for a previously unproved substitution rule. -/

#check OSR.IntegrationRec207.rubi312r2Nondeg_real
#check OSR.IntegrationRec208.rubi312r2Nondeg_counterexample_complex
#check OSR.IntegrationRec209.rubi312r7Nondeg_real
#check OSR.IntegrationRec209.rubi312r7Nondeg_complex

#guard (OSR.Registry.mappingAssurance OSR.IntegrationNum1.rubi312r7Nondeg.symbols .real).certifiable
#guard (OSR.Registry.mappingAssurance OSR.IntegrationNum1.rubi312r7Nondeg.symbols .complex).certifiable
