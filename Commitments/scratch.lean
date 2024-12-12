import Mathlib

-- Attempt to prove exp_bij in Lean 4 drawn from Cryptolib
variable {G: Type*} [Fintype G] [Group G] [DecidableEq G] [IsCyclic G]
variable (q : ℕ) [Fact (Nat.Prime q)] 
variable (G_card_q : Fintype.card G = q)
variable (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)

@[simp] theorem intCast_natMod (a b : Int) [NeZero b] : (a.natMod b : Int) = a % b := by
  simpa [Int.natMod] using Int.emod_nonneg _ (NeZero.ne b)

@[simp] theorem ZMod.val_intCast' {n : ℕ} (a : ℤ) [NeZero n] : (a : ZMod n).val = Int.natMod a n := by
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_coe]
  rw [ZMod.val_intCast]
  simp

theorem Int.natMod_eq_sub (x w : Int) (h : w ≠ 0) : Int.natMod x w = x - w * (x / w) := by
  plausible

include G_card_q
include g_gen_G

lemma exp_bij : Function.Bijective fun (z : ZMod q) => g^z.val := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  have h_prime : q.Prime := Fact.out 
  have h_card : g ^ q = 1 := by
    rw [←G_card_q]
    apply pow_card_eq_one 
  simp [h_card, G_card_q]
  intro y 
  obtain ⟨k, hk⟩ := g_gen_G y
  use k 
  have h_pow : g^((k : ZMod q).val) = y := by
    subst hk G_card_q
    simp_all only [pow_card_eq_one, zpow_mod_card]
    simp_all only [ZMod.val_intCast']
    rw [←zpow_natCast]
    rw [Int.natMod_eq_sub]
    · rw [zpow_sub]
      rw [zpow_mul]
      --rw [zpow_natCast]
      --rw [pow_card_eq_one]
      simp
    · simp
  exact h_pow

  

