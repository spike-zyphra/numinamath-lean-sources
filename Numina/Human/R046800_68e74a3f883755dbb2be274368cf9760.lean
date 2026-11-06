import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

/-Find the value of the real number $x$ such that the complex number $z=\log_{2}(x^{2}-3x-2)+i\log_{2}(x-3)$ is a real number.-/
theorem algebra_9103 (x : ℝ) (hx : 3 < x): x = 4 ↔
∃ z : ℝ, logb 2 (x^2 - 3 * x - 2) + I * logb 2 (x - 3) = z := by
-- Break "iff"
  constructor
-- Check when $x=4$, the assumption is satisfied
  · intro hx; use 1; rw [hx]; norm_num
-- Conversely, assume we have a real number $w$ satisfies the assumption
-- then the imaginary part has to be $0$ and we can solve for $x$
  rintro ⟨w, hw⟩; rw [Complex.ext_iff] at hw
  simp at hw; rcases hw with ⟨_, r1|r2|r3⟩
  · linarith
  · rw [sub_eq_zero] at r2; linarith
  cases r3; rename_i r3
  rw [sub_eq_iff_eq_add, show (1:ℝ)+3=4 by norm_num] at r3; assumption
  linarith