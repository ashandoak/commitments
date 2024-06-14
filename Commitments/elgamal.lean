import Mathlib

namespace ElGamal

variable (G : Type) [Fintype G] [Group G] -- Ensures Fintype and Group ensures nonempty 
variable (q : ℕ) [NeZero q] -- No need for this to be declared prime; this will come through with the DDH assumption 
variable (g : G) -- g is any fixed generator

noncomputable section

def uniform_grp : PMF G := PMF.uniformOfFintype G -- A uniform distribution giving all elementst of G probability 1/|G|. Both Group G and Fintype G required here.

theorem zmod_nonempty {t : ℕ} [NeZero t] : (ZMod.fintype t).elems.Nonempty := by -- hmm.. Nonempty is classical - perhaps a different route?
  have h' : 0 < (ZMod.fintype t).elems.card := by sorry
  sorry 

def keygen : PMF (G × ZMod q) := -- This works when G, Type, Fintype, Group is provided as a variable
do
  let h ← PMF.uniformOfFinset (ZMod.fintype q).elems zmod_nonempty
  pure (g^h.val, h) -- Why does `val` work here?

#check keygen
#check keygen _ _ _
#check keygen ?_ ..
#check (keygen _ _ _).1 
#check keygen G q g 

def keygen' {G : Type} [Fintype G] [Group G] : PMF (G × ZMod q) := -- This "works" when G not defined as a variable, but can't resolve the final HPow
do
  let h ← PMF.uniformOfFinset (ZMod.fintype q).elems zmod_nonempty
  pure (g^h, h) -- Why does `val` work here?

#check keygen'
#check keygen' _

def keygen'' (g : G) : PMF (G × ZMod q) := -- This "works" when G not defined as a variable, but can't resolve the final HPow
do
  let h ← PMF.uniformOfFinset (ZMod.fintype q).elems zmod_nonempty
  pure (g^h, h) -- Why does `val` work here?

#check keygen''
#check keygen'' _ _
#check keygen'' 3 _
variable (m : H)
#check keygen'' 3 m

def keygen₁ : PMF (G × ZMod q) :=
do
  let h ← PMF.uniformOfFintype (ZMod q) -- Becasue ZMod has a Fintype instance? 
  pure (g^h.val, h) -- Why does `val` work here?

set_option pp.all true
set_option diagnostics true
#check keygen₁
#check @keygen₁
#print keygen₁








-- Later...


def keygen' : PMF (G × ZMod q) :=
do
  let x ← uniform_zmod q
  pure (gen_g^x.val, x)

def commit₁ (m : G) (h : G) : ((Zmod q) × G × G) := by
  obtain r : ZMod q := sorry -- uniform?
  exact (r, gen_g^r, m*h^r) -- pass h in rather than using def gen_h

def open₁ (m : G) (r : ZMod q) (c : G × G) : Prop := by
  let c' := ⟨gen_g^r, m*gen_h^r⟩
  exact c' = c

lemma isBinding (c : G × G) (m m' : G) : m = m' := by
  let r₁ := (commit₁ m).1   
  let c₂ := ⟨gen_g^r', m'*gen_h^r'⟩ 
  have hc₁c₂ : c₁ = c₂ := by sorry
  have hgen_g : c₁.1 = c₂.1 := by sorry
  have hgen_h : gen_h^r = gen_h^r' := by sorry
  simp


-- Proof that if g is a generator g^r = g_r' <=> r = r'
end ElGamal
