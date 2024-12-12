import Mathlib

noncomputable section
variable (G : Type) [Fintype G] [Group G] [DecidableEq G] 
variable (q : ℕ) [NeZero q] (hq : q > 1) -- No need for this to be declared prime; this will come through with the DDH assumption
variable (g : G) -- g is any fixed generator

variable (setup : PMF G)
         (adversary : G → PMF (ZMod q))

def DLog : PMF (ZMod 2) :=
do
  let h ← setup  
  let x ← adversary h 
  if g^x.val = h then pure 1 else pure 0
