import Mathlib

open Real

theorem inequalities_90405 : IsGreatest {x : ℝ | ∃(a b : ℝ), 0 < a ∧ 0 < b ∧ a^5 + b^5 = a^3 + b^3 ∧ x = a^2 - a * b + b^2} 1 := by
  constructor
  · use 1, 1
    norm_num
  · -- Show that if $r$ is in the set, then $r \leq 1$.
    intro r hr
    rcases hr with ⟨a, b, ha, hb, h, hr⟩
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 1)]