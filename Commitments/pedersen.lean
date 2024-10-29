import Mathlib

noncomputable section

/-
\ variable (setup : PMF K)
         (commit : K → M → PMF (C × O))
         (verify : K → M → C × O → ZMod 2)
         (adversary : K → PMF (C × M × M × O × O))
-/


variable {G : Type} [Fintype G] [Group G] [HPow G G G] [DecidableEq G] 
variable (q : ℕ) [NeZero q] -- No need for this to be declared prime; this will come through with the DDH assumption
variable {g : G} -- g is any fixed generator


namespace Pedersen

def setup : PMF G :=
do
  let h ← PMF.uniformOfFintype G 
  return h 

def commit (h : G) (m : G) : PMF (G × ZMod q) :=
do
  let r ← PMF.uniformOfFintype (ZMod q)
  return (g^m * h^r.val, r)
  
def verify (h : G) (m : G) (c : (G × ZMod q)) : Prop :=
  if c.1 = g^m * h^c.2.val then true else false


