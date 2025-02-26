import Mathlib

namespace DLog

noncomputable section

variable (G : Type) [Fintype G] [Group G] [DecidableEq G] 
variable (q : ℕ) [NeZero q] (hq : q > 1) -- No need for this to be declared prime; this will come through with the DDH assumption
variable (g : G) -- g is any fixed generator

-- Modification of Attack game and advantage as specified in Boneh 10.4 to account for check between generated x and x'
def attack_game (A : G → PMF (ZMod q)) : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod q)
  let x' ← A (g^x.val)
  pure (if x = x' then 1 else 0)

-- The advantage of an attacker A in the DLog problem
-- attack_game returns a PMF ()
def advantage (A : G → PMF (ZMod q)) : ENNReal := attack_game G q g A 1 
end

end DLog

