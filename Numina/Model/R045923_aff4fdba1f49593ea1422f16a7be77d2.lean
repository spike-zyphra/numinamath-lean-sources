import Mathlib

theorem inequalities_207837 (x y z : ℝ) :
    ¬(|x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y|) := by
  intro h
  rcases h with ⟨h1, h2, h3⟩
  have h4 : x ^ 2 < (y - z) ^ 2 := by
    apply sq_lt_sq.2
    exact h1
  have h5 : y ^ 2 < (z - x) ^ 2 := by
    apply sq_lt_sq.2
    exact h2
  have h6 : z ^ 2 < (x - y) ^ 2 := by
    apply sq_lt_sq.2
    exact h3
  nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
          sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
          abs_nonneg (x - y), abs_nonneg (y - z), abs_nonneg (z - x)]