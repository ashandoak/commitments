import Mathlib

noncomputable section

-- Spaces for messages (M), commitments (C), opening values (O) and keys (K)
variable {M C O K : Type}  

variable (setup : K)
         (commit : K → M → C × O)
         (verify : K → M → C × O → ZMod 2)
