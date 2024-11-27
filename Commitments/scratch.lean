import Mathlib

-- Attempt to prove exp_bij in Lean 4 drawn from Cryptolib
variable {G: Type*} [Fintype G] [Group G] [DecidableEq G] [IsCyclic G]
variable (q : ℕ) [Fact (Nat.Prime q)] 
variable (G_card_q : Fintype.card G = q)
variable (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)

lemma exp_bij : Function.Bijective fun (z : ZMod q) => g^z.val := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  have h_prime : q.Prime := Fact.out --cases q
  have h_card : g ^ q = 1 := by
    rw [←G_card_q]
    apply pow_card_eq_one
  simp [*]
  --simp_all only [and_true] -- This works because of G_card_q
  intro y
  obtain ⟨k, hk⟩ := g_gen_G y
  use (k : ZMod q)
  --simp_all only
  have h_pow : g^((k : ZMod q).val) = y := by
    -- The key is to connect k, k mod q, and y
    have h_mod : g^k = g^(k % q) := by
      apply zpow_eq_zpow_emod' _ h_card
    rw [h_mod]
    exact hk
  exact h_pow

  /-
  have h1 : g^((k : ZMod q).val) = g^k := by 
    have h_mod : (k : ZMod q) = k % q := by 
      simp_all only [CharP.cast_eq_zero, EuclideanDomain.mod_zero]
    rw [h_mod]
    have h_cyclic : (k : ZMod q) % q = k := by 
      exact id (Eq.symm h_mod)
    rw [h_cyclic]
    have h_card : g ^ q = 1 := by
      rw [←G_card_q]
      apply pow_card_eq_one
    have h_pow_equiv : g^k = g^(k % q) := by 
      apply zpow_eq_zpow_emod' _ h_card
    have h_eff : g^(k : ZMod q).val = g^(k % q):= by 
      simp_all only [CharP.cast_eq_zero, EuclideanDomain.mod_zero]
      exact h_pow_equiv  
    rw [h_pow_equiv]
    exact h_eff 
  rw [←hk]
  exact h1 
  -/

/-
  let (g, hG) := IsCyclic.exists_generator (α := G)
  exact (Subgroup.mem_zpowers_iff).mp (hG g)
  have h := (Subgroup.mem_zpowers_iff).mp h' _
  simp only [ZMod.card]
-/

example : Function.Surjective fun (z : ZMod q) => g^z.val := by 
  intro gz
  obtain ⟨k, hk⟩ := g_gen_G gz
  use (k : ZMod q)
  simp
  have h1 : g^(k % q) = g^k := by 
    aesop 
  rw [h1]
  --exact hk
  
  
/-
  simp_all only 
  intro y
  have hz := Subgroup.mem_zpowers_iff.mp (g_gen_G gz) 
  cases hz with 
-/  

example (x : ℕ) : ((x : ℤ) = ↑x) := rfl

example : Fintype.card (ZMod q) = Fintype.card G := by
   cases q
   aesop 
   simp
   linarith -- This works because of G_card_q

#check NeZero 0
#reduce NeZero 0  
