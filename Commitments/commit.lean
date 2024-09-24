import Mathlib

noncomputable section

-- Spaces for messages (M), commitments (C), opening values (O) and keys (K)
variable {M C O K : Type}  

variable (setup : PMF K)
         (commit : K → M → PMF (C × O))
         (verify : K → M → C × O → ZMod 2)

-- TODO add in commit_verify to be used in correctness
-- TODO fix to make use of PMF and commiy_verify
def correctness : Prop := ∀ (m : M), verify setup m (commit setup m) = 1 

-- theorem correctness' :  ∀ (m : M), verify setup m (commit setup m) = 1 := sorry 
