import Mathlib

variable {G : Type} [Fintype G] [Group G] -- Ensures Fintype and Group ensures nonempty 
variable (q : ℕ) [NeZero q] -- No need for this to be declared prime; this will come through with the DDH assumption 
variable {g : G} -- g is any fixed generator

noncomputable section

namespace ElGamal

-- Not presently needed...
/-
def uniform_grp : PMF G := PMF.uniformOfFintype G -- A uniform distribution giving all elementst of G probability 1/|G|. Both Group G and Fintype G required here.

theorem zmod_nonempty {t : ℕ} [NeZero t] : (ZMod.fintype t).elems.Nonempty := by -- hmm.. Nonempty is classical - perhaps a different route?
  have h' : 0 < (ZMod.fintype t).elems.card := by sorry
  sorry 
-/

def keygen : PMF (G × ZMod q) :=
do
  let s ← PMF.uniformOfFintype (ZMod q) 
  return (g^s.val, s)

-- Reversing the order of the opening value and the commitment since Lean projection notation is right associative
def commit (h : G) (m : G) : PMF ((ZMod q) × G × G) :=
do
  let r ← PMF.uniformOfFintype (ZMod q)
  return (r, g^r.val, m*h^r.val)
  
def verify (h : G) (m : G) (c : G × G) (o : ZMod q) : Prop := by
  let c' := (g^o.val, m*h^o.val)   
  exact c' = c
/-
-- TODO: Check to see what Decidable typeclass could be used here?
def verify' (h : G) (m : G) (c : PMF (G × G)) (o : PMF (ZMod q)) : PMF Bool := 
do  
  let o' ← o
  let c' ← c
  let cc := (g^o'.val, m*h^o'.val) 
  return if cc = c' then true else false

def verify'' (h : G) (m : G) (c : PMF (G × G)) (o : PMF (ZMod q)) : Prop := 
  (c >>= fun x => return c.1)

def verify''' (h : G) (m : G) (c : G × G) (o : ZMod q) : ZMod 2 := sorry 

variable (g' t k : G) [Group G]
variable (q' : ℕ) [NeZero q']
#check keygen
#check @commit G _ q' _ g' t k
#check commit q' t k
#check (commit q' t k).1
#check (commit q' t k).2
#check verify q' t k _ _
#check verify' q t k (commit q t k >>= fun x => return x.2) (commit q t k >>= fun x => return x.1)

def commit_verify (m : G) : :=
do
  h ← keygen q
  c ← commit q h m
  verify' q  



-- Not sure what the best approach to proving this is - straight proof term?

theorem correctness : ∀ m h : G, verify q h m (commit q h m) (commit q h m).1 = true :=
do
  let c ← (commit₁ h m).1
  verify h m c.1 (c.2, c.3) := by
  let r := c.1
  let c' := (g^r.val, m*h^r.val)
  exact c' = (c.2, c.3)

theorem correctness' : ∀ m h : G, verify' q t k (commit q t k >>= fun x => return x.2) (commit q t k >>= fun x => return x.1) = true := sorry
/-
lemma isBinding (c : G × G) (m m' : G) : m = m' := by
  let r₁ := (commit m).1   
  let c₂ := ⟨gen_g^r', m'*gen_h^r'⟩ 
  have hc₁c₂ : c₁ = c₂ := by sorry
  have hgen_g : c₁.1 = c₂.1 := by sorry
  have hgen_h : gen_h^r = gen_h^r' := by sorry
  simp
-/

-- Proof that if g is a generator g^r = g_r' <=> r = r'
-/
end ElGamal

