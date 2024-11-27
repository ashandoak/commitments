import Mathlib.Probability.Distributions.Gaussian

open MeasureTheory ProbabilityTheory

-- From https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Should.20.22sampling.22.20be.20non.20computable.3F/near/476959834

def I : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1}
variable {Y : I → ℝ} (hY : Measure.map Y ν = gaussianReal 0 1)
def x : I := ⟨0.5, ⟨by norm_num, by norm_num⟩⟩

#reduce Y x

-- Y
--   ⟨{
--       cauchy :=
--         Quot.mk (fun f g ↦ (f - g).LimZero) ⟨fun x ↦ { num := Int.ofNat 1, den := 2, den_nz := ⋯, reduced := ⋯ }, ⋯⟩ },
--     x.proof_1⟩

#reduce (proofs := true) Y x

-- (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
-- Use `set_option maxHeartbeats <num>` to set the limit.

