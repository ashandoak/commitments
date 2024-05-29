import Mathlib

namespace ElGamal

variable (G : Type*) [Fintype G] [Group G] [IsCyclic G]
variable (q : ℕ) [Fact q.Prime] -- Comes thru with DDH - primality of q is implicit
-- better: variable (g : G) -- can be any fixed generator

def G_card_is_Zq : Prop := by sorry

def gen_g : G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
  exact g

def gen_h : G := by
  -- obtain ⟨h, hh⟩ := IsCyclic.exists_generator
  -- exact h
  -- obtain a uniform x - similar to keygen for elgamal less the secret key
  -- obtain h by raising g to x
  -- return h

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
