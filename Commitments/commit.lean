import Mathlib

noncomputable section

variable {G : Type}  

variable (keygen : PMF (G × G))
         (commit : G → G → PMF (G × G × G))
         (verify : G → G → G × G × G → ZMod 2)

def commit_verify (m : G) : PMF (ZMod 2) :=
do
  let h ← keygen >>= fun x => return x.1
  let c ← commit h m
  return verify h m c

def commit_verify_correct : Prop := ∀ (m : G), commit_verify keygen commit verify m = return 1
