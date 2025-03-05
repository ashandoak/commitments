import Mathlib
import Commitments.dlog
import Commitments.commit

noncomputable section

variable {G : Type} [Fintype G] [Group G] [DecidableEq G] 
-- variable (q : ℕ) [Fact (Nat.Prime q)] -- per note below - I'm using this in the scratch file in the proof of exp_bij
variable (q : ℕ) [NeZero q] (hq : q > 1) -- No need for this to be declared prime; this will come through with the DDH assumption
variable (g : G) -- g is any fixed generator

variable (A : G → PMF ((G × ZMod q) × ZMod q × ZMod q × ZMod q × ZMod q))

include G q g

namespace Pedersen

def setup : PMF G :=
do
  let k := Finset.Icc 1 (q-1)
  have k_nonempty : k.Nonempty := by 
    refine Finset.nonempty_Icc.mpr ?_
    omega
  let a ← PMF.uniformOfFinset k k_nonempty
  return g^a


def commit (h : G) (m : ZMod q) : PMF (G × ZMod q) :=
do
  let r ← PMF.uniformOfFintype (ZMod q)
  return (g^m.val * h^r.val, r)


def verify (h : G) (m : ZMod q) (c : (G × ZMod q)) : Prop :=
  if c.1 = g^m.val * h^c.2.val then true else false


def negligible (f : ℕ → ℝ) : Prop :=
  ∀ c > 0, ∃ n₀, ∀ n ≥ n₀, f n < 1 / (n ^ c)
/-
lemma computationallyBinding : 
  ∀ (Adversary : G → PMF ((G × ZMod q) × ZMod q × ZMod q × ZMod q × ZMod q)), 
  ∃ (negligible_prob : ℕ → ℝ),
    negligible negligible_prob ∧
    ∀ (n : ℕ), Pr[compBind] ≤ negligible_prob n := sorry

open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable (P : Measure ENNReal) (s : Set ENNReal)

#check P s

--lemma comp_bind : ∀ a : A, computational_binding 
#check verify  
#check computational_binding (compBind (setup q hq g) (verify G q (G × ZMod q))  _)

-- def perfect_hiding' : Prop := ∀ (m m' : M), ∀ (c : C), do_commit setup commit m c = do_commit setup commit m' c
-- TODO lemma: do_commit setup commit m c = 1 / the cardinality as a step toward perfect hiding

def perfect_hiding : Prop := ∀ (m m' : ZMod q), ∀ (c : G × ZMod q), commit (setup q hq g) m c = commit (setup q hq g) m' c  

#check Commit.perfect_hiding $ Commit.do_commit setup commit

-- TODO Try to match this to what Lupo is doing, but note the missing enc_dec function in his proof of elgamal correctness
-- TODO Why does Lupo's elgamal correctness typecheck?
theorem perfect_hiding' : Commit.perfect_hiding Commit.do_commit  := by sorry
-/
