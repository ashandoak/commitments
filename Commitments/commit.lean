import Mathlib

noncomputable section

-- Spaces for messages (M), commitments (C), opening values (O) and keys (K)
variable {M C O K : Type}  

variable (setup : PMF K)
         (commit : K → M → PMF (C × O))
         (verify : K → M → C × O → ZMod 2)

def commit_verify (m : M) : PMF (ZMod 2) :=
do
  let k ← setup
  let c ← commit k m
  return (verify k m c)


def correctness : Prop := ∀ (m : M), commit_verify setup commit verify m = pure 1  


def perfect_binding : Prop := 
  ∀ (h : K) (c : C) (m m' : M) (o o' : O), 
    if verify h m ⟨c,o⟩ = verify h m' ⟨c, o'⟩ then true else false 

-- This seems wrong... binding_adversary should get setup parameters, not a key, but we've declared K as the key space...?
def binding_adversary (h : K) : PMF (C × M × M × O × O) := 
do
  let c ← sorry
  let m ← sorry
  let m' ← sorry
  let o ← sorry
  let o' ← sorry
  return ⟨c, m, m', o, o'⟩


/-
def computational_binding (h : K) : Prop :=
  ∀ A : binding_adversary -- but this doesn't work because binding_adversary is not a type... 
-/

structure Binding_Adversary (h : K) where
  c : C
  m : M
  m' : M
  o : O
  o' : O

def computational_binding (h : K) : Prop :=
  ∀ A : Binding_Adversary h,
    if verify h A.m ⟨A.c, A.o⟩ = verify h A.m' ⟨A.c, A.o'⟩
      then if A.m != A.m' then true else false
      else false


def perfect_hiding : PMF Prop :=
  ∀ (m m' : M) (c : C),
    let h := setup
    let commit₁ := commit h m
    let commit₂ := commit h m'
    do
      if commit₁.1 = c then true else false
