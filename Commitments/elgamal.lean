import Mathlib

variable (G : Type) [Fintype G] [Group G] -- Ensures Fintype and Group ensures nonempty 
variable (q : ℕ) [NeZero q] -- No need for this to be declared prime; this will come through with the DDH assumption 
variable (g : G) -- g is any fixed generator

noncomputable section

namespace ElGamal

def uniform_grp : PMF G := PMF.uniformOfFintype G -- A uniform distribution giving all elementst of G probability 1/|G|. Both Group G and Fintype G required here.

theorem zmod_nonempty {t : ℕ} [NeZero t] : (ZMod.fintype t).elems.Nonempty := by -- hmm.. Nonempty is classical - perhaps a different route?
  have h' : 0 < (ZMod.fintype t).elems.card := by sorry
  sorry 

-- This seems like the right direction
def keygen : PMF (G × ZMod q) :=
do
  let h ← PMF.uniformOfFintype (ZMod q) -- Becasue ZMod has a Fintype instance?  TODO: Change h to s
  pure (g^h.val, h) -- Why does `val` work here? Because we're using do notation here, and the wrapped ZMod q is "assigned" to h, so h *isn't* a PMF

def commit (m : G) (h : G) : PMF (ZMod q × G × G) :=
do
  let r ← PMF.uniformOfFintype (ZMod q)
  pure (r, g^r.val, m*h^r.val) -- pass h in rather than using def gen_h

def verify (h : G) (m : G) (r : ZMod q) (c : G × G) : Prop := by
  let c' := (g^r.val, m*h^r.val)   
  exact c' = c

theorem correctness (m : G) (h : G) := -- TODO: Clean this up
do
  let c ← (commit₁ m h).1
  verify₁ h m c.1 (c.2, c.3) := by
  let r := c.1
  let c' := (g^r.val, m*h^r.val)
  exact c' = (c.2, c.3)


lemma isBinding (c : G × G) (m m' : G) : m = m' := by
  let r₁ := (commit m).1   
  let c₂ := ⟨gen_g^r', m'*gen_h^r'⟩ 
  have hc₁c₂ : c₁ = c₂ := by sorry
  have hgen_g : c₁.1 = c₂.1 := by sorry
  have hgen_h : gen_h^r = gen_h^r' := by sorry
  simp


-- Proof that if g is a generator g^r = g_r' <=> r = r'
end ElGamal
