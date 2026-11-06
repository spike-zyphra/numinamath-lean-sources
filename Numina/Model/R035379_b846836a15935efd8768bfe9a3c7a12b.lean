import Mathlib

open Real

theorem inequalities_110694 (x y z : ℝ) :
    x^2 + y^2 + z^2 ≥ x * y + y * z + z * x ∧
    ∀ t ∈ Set.Icc (-1) 2, x^2 + y^2 + z^2 + t * (x * y + y * z + z * x) ≥ 0 := by
  constructor
  · -- Prove that $x^2 + y^2 + z^2 \geq x * y + y * z + z * x$.
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- Show that for all $t \in [-1, 2]$, $x^2 + y^2 + z^2 + t * (x * y + y * z + z * x) \geq 0$.
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z), sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z),
      mul_nonneg (show (0 : ℝ) ≤ 2 - t by linarith) (show (0 : ℝ) ≤ t + 1 by linarith)]