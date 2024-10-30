import Mathlib

noncomputable section

/-
\ variable (setup : PMF K)
         (commit : K → M → PMF (C × O))
         (verify : K → M → C × O → ZMod 2)
         (adversary : K → PMF (C × M × M × O × O))
-/


variable {G : Type} [Fintype G] [Group G] [DecidableEq G] 
variable (q : ℕ) [NeZero q] -- No need for this to be declared prime; this will come through with the DDH assumption
variable {g : G} -- g is any fixed generator


namespace Pedersen

def setup : PMF G :=
do
  let h ← PMF.uniformOfFintype G 
  return h 

def commit (h : G) (m : ZMod q) : PMF (G × ZMod q) :=
do
  let r ← PMF.uniformOfFintype (ZMod q)
  return (g^m.val * h^r.val, r)
 
-- TODO Return ZMod 2
def verify (h : G) (m : ZMod q) (c : (G × ZMod q)) : Prop :=
  if c.1 = g^m.val * h^c.2.val then true else false


