import Mathlib

theorem inequalities_261898 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 4 + b ^ 4 + c ^ 4) / (a * b * c) := by
  have h1 : 0 < a * b * c := by positivity
  suffices (a + b + c) * (a * b * c) ≤ a ^ 4 + b ^ 4 + c ^ 4 by
    exact (le_div_iff₀ h1).mpr this
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]