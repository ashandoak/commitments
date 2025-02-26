import Mathlib
import Commitments.«cryptolib-pke»

namespace cryptolib
--variables {α β : Type}

lemma bind_skip (p : PMF α) (f g : α → PMF β) : 
  (∀ (a : α), f a = g a) → p.bind f = p.bind g := by
  intro ha 
  ext
  simp
  simp_rw [ha]

lemma bind_skip_const (pa : PMF α) (pb : PMF β) (f : α → PMF β) : 
  (∀ (a : α), f a = pb) → pa.bind f = pb := by
  intro ha 
  ext
  simp
  simp_rw [ha]
  simp [ENNReal.tsum_mul_right]

end cryptolib

noncomputable section
namespace elgamal
variable {G : Type} [Fintype G] [CommGroup G] [DecidableEq G] 
         (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [NeZero q] (hq : q > 1)(G_card_q : Fintype.card G = q) 
         (A_state : Type)

include g_gen_G G_card_q

variable (A1 : G → PMF (G × G × A_state))
         (A2 : G → G → A_state → PMF (ZMod 2))
           
def A2' : G × G → A_state → PMF (ZMod 2) := fun (gg : G × G) => A2 gg.1 gg.2

-- generates a public key `g^x.val`, and private key `x`
def keygen : PMF (G × (ZMod q)) := 
do 
  let x ← PMF.uniformOfFintype (ZMod q)
  pure (g^x.val, x) 

#check keygen
-- encrypt takes a pair (public key, message)
def encrypt (pk m : G) : PMF (G × G) := 
do
  let y ← PMF.uniformOfFintype (ZMod q)
  pure (g^y.val, pk^y.val * m)

-- `x` is the secret key, `c.1` is g^y, the first part of the 
-- cipher text returned from encrypt, and `c.2` is the 
-- second value returned from encrypt
def decrypt (x : ZMod q) (c : G × G) : G := (c.2 / (c.1^x.val))

#check encrypt

lemma decrypt_eq_m (m : G) (x y: ZMod q) : decrypt q x ((g^y.val), ((g^x.val)^y.val * m)) = m := by
  simp only [decrypt]
  rw [mul_comm]
  rw [← npow_mul] 
  rw [← npow_mul] 
  rw [div_eq_iff_eq_mul]
  rw [mul_comm x.val y.val] 

#check keygen 

theorem elgamal_correctness : PKE.pke_correctness (keygen g q) (@encrypt _ _ g q _) (@decrypt _ _ _) := by
  simp only [PKE.pke_correctness]
  intro m
  simp [PKE.enc_dec] 
  simp [keygen]
  simp [encrypt]
  simp [decrypt]
  apply cryptolib.bind_skip_const
  intro a
  simp [pure]
  apply cryptolib.bind_skip_const
  intro b
  simp
  rw [pow_right_comm]
  simp



end elgamal
