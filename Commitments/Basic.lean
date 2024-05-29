import Mathlib

variable (n : ℕ)
-- use of Fact seems justified here: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#Fact
variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
-- variable (G : Type*) [Group G] [Fintype G]

-- From: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Hypotheses.20on.20a.20group/near/244596727 
-- variables {G : Type} [fintype G] [group G] [is_cyclic G]
-- variables (g : G) (hGg : ∀ (x : G), x ∈ subgroup.gpowers g)
-- variables (q : ℕ) (q_pos : 0 < q) (hGq : fintype.card G = q)

-- Suggestion for obtaining a witness
-- obtain ⟨g, hg⟩ := is_cyclic.exists_generator

-- From cryptolib (final version derived from the above)
-- (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
-- (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g)
-- (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q)

-- Lean 4 version of the above
variable (G : Type*) [Fintype G] [CommGroup G] 
         (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [Fact (0 < q)] (G_card_q : Fintype.card G = q)

#check g_gen_G
#check G_card_q

variable (p r : ℕ)(G : ZMod (p ^ r)) [h₀ : Fact (p.Prime)]

-- I don't think this is useful, since I don't need a full set of generators
-- def generators : Set (ZMod (p ^ r)) :=
--  {n | AddSubgroup.zmultiples n = ⊤}

def commit₁ (u : ZMod n) (x : ℕ) : ZMod n := sorry --g^h * h^x


-- El Gamal binding
-- I just found these notes that mention “El Gamal” commitments. I don’t know if this is standard terminology, but anyway the idea is very simple – to
-- commit to M choose a random r and send (c,c’) (g^r, Mh^r) (i.e. pretty much an El Gamal ciphertext – but there is no “key”.)
-- To open just send M,r and check that c=g^r and c’=Mh^r.
-- (Computational) hiding comes from the fact that El Gamal has indistinguishable encryptions.
-- Binding is “perfect” and follows almost directly. Suppose (g^r’,M’h^r’)=(g^r,Mh^r). Since g is a generator, this means r=r’. But then h^r’=h^r, so from M’h^r’=Mh^r we can conclude M=M’.



