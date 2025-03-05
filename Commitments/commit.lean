import Mathlib

noncomputable section

namespace Commit
-- Spaces for messages (M), commitments (C), opening values (O) and keys (K)
variable {M C O K : Type} [DecidableEq M] 

variable (setup : PMF K)
         (commit : K → M → PMF (C × O))
         (verify : K → M → C × O → ZMod 2)
         (adversary : K → PMF (C × M × M × O × O))

def commit_verify (m : M) : PMF (ZMod 2) :=
do
  let k ← setup
  let (c, o) ← commit k m
  return (verify k m ⟨c, o⟩)

-- TODO What does equality between PMFs actually mean? 
-- Lupo uses extensionality (make sense) and the Monadic laws to argue equivalence between PMFs, but I don't quite understand why.
-- TODO Does FCF or Nowak's toolkit provide more clarity re: PMF equivalence?
def correctness : Prop := ∀ (m : M), commit_verify setup commit verify m = pure 1  


def perfect_binding : Prop := 
  ∀ (h : K) (c : C) (m m' : M) (o o' : O), 
    if verify h m ⟨c,o⟩ = verify h m' ⟨c, o'⟩ then true else false 

-- Helper function that can be used to define compuational binding 
def compBind : PMF (ZMod 2) :=
do
  let h ← setup
  let (c, m, m', o, o') ← adversary h
  if verify h m ⟨c,o⟩ = 1 ∧ verify h m' ⟨c, o'⟩ = 1 ∧ m ≠ m' then pure 1 else pure 0 

-- TODO Figure out if we can use pattern matching rather than projections. Note Lupo's point on page 16
-- if verify h b.2.1 ⟨b.1, b.2.2.2.1⟩ = verify h b.2.2.1 ⟨b.1, b.2.2.2.2⟩ then pure 1 else pure 0 

def computational_binding (ε : ENNReal) : Prop := compBind setup verify adversary 1  < ε

-- compBind returns a PMF ZMod 2
#check compBind setup verify adversary 

-- Wrapping a Nat in a PMF produces a PMF ℕ
#check PMF.pure 1

-- Passing a ℕ to the PMF ℕ returns an ENNReal, since PMF is a function α → ENNReal
#check PMF.pure 1 1

-- Similarly, wrapping a String in a PMF produces the distribution where "a" is assigned probability 1 and all other values are assigned probability 0
#check PMF.pure "a" "b"

-- So we should be able to check the resulting probability value for any given element of the presumed set
#check PMF.pure "a" "b" = 1


def do_commit (m : M) : PMF C :=
do
  let h ← setup
  let (c, _) ← commit h m
  return c

-- TODO How to get the notion of a distribtuion into a Prop?
def perfect_hiding : Prop := ∀ (m m' : M), ∀ (c : C), do_commit setup commit m c = do_commit setup commit m' c
