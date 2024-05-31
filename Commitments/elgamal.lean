import Mathlib


namespace ElGamal

variable (G : Type*) [Fintype G] -- [Group G] [IsCyclic G]
deriving instance Fintype for Monoid 

variable (q : ℕ) -- No need for this to be declared prime; this will come through with the DDH assumption

variable (g : G) -- g is any fixed generator

-- Proof that the cardinality of G is Zq - is this necessary?
def G_card_is_Zq : Prop := by sorry

variable (H : Type*) [Group H]
-- instance : Fintype (Group H)  := by sorry
deriving instance Fintype for Group
variable (h : H)
#check h.elems


def keygen : PMF (G × ZMod q) :=
do
  x ← uniform_zmod q
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
end ElGamalt
