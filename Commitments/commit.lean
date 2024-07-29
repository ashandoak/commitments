-- TODO: Add abstract variables to represent commit verify and keygen
-- TODO: commit_verify that returns ZMod 2
-- TODO: Cross reference Lupo chapter 3

import Mathlib

variable {G : Type} [Group G] [Fintype G] 
         {q : ℕ} [NeZero q]
         {g : G}

variable (keygen : PMF (G × ZMod q))
         (commit : G → G → PMF ((ZMod q) × G × G))
         (verify : G → G → G × G → ZMod q → Prop)


def commit_verify (m : G) : PMF ℕ  :=
do
  -- let h ← keygen.1 -- TODO: Why does this result in a metavariable?
  let h := keygen >>= fun x => return x.1
  let c :=
  do
    let h' ← h
    commit h' m
  let b :=
  do
    let h' ← h
    let c' ← c
    pure c'
  return (if (verify h' m c'.2 c'.1 = true) then 1 else 0)


