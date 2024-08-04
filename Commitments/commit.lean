-- TODO: commit_verify that returns ZMod 2
-- TODO: Cross reference Lupo chapter 3

import Mathlib

noncomputable section

variable {G : Type} [Group G] [Fintype G] 
         {q : ℕ} [NeZero q]
         {g : G}

variable (keygen : PMF (G × ZMod q))
         (commit : G → G → PMF ((ZMod q) × G × G))
         (verify : G → G → (ZMod q) × G × G → Prop)

def commit_verify' (m : G) : PMF Prop :=
do
  let h ← keygen >>= fun x => return x.1
  let c ← commit h m
  return verify h m c
