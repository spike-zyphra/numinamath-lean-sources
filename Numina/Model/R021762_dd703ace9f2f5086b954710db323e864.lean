import Mathlib

open Real

theorem inequalities_8175 {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (P : ℝ → ℝ) (hP : P = fun x => ∑ k in Finset.range 3, a k * x ^ k) :
    ∀ x y, (P (x * y)) ^ 2 ≤ P (x ^ 2) * P (y ^ 2) := by

  intro x y
  have h1 : P (x * y) = a 0 + a 1 * (x * y) + a 2 * (x * y) ^ 2 := by
    rw [hP]
    simp [Finset.sum_range_succ]
    all_goals norm_num

  have h2 : P (x ^ 2) = a 0 + a 1 * (x ^ 2) + a 2 * (x ^ 2) ^ 2 := by
    rw [hP]
    simp [Finset.sum_range_succ]
    all_goals norm_num

  have h3 : P (y ^ 2) = a 0 + a 1 * (y ^ 2) + a 2 * (y ^ 2) ^ 2 := by
    rw [hP]
    simp [Finset.sum_range_succ]
    all_goals norm_num
  
  rw [h1, h2, h3]
  have ha0 : 0 ≤ a 0 := ha 0
  have ha1 : 0 ≤ a 1 := ha 1
  have ha2 : 0 ≤ a 2 := ha 2
  
  nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2),
    sq_nonneg (a 0 - a 1 * x * y), sq_nonneg (a 0 - a 1 * x^2), sq_nonneg (a 0 - a 1 * y^2),
    sq_nonneg (a 1 * x * y - a 2 * (x * y)^2), sq_nonneg (a 1 * x^2 - a 2 * x^4), sq_nonneg (a 1 * y^2 - a 2 * y^4),
    sq_nonneg (a 1 * (x^2 - y^2)), sq_nonneg (a 2 * (x^2 - y^2) * (x^2 + y^2)),
    sq_nonneg (x * y), sq_nonneg (x^2 - y^2), mul_nonneg ha0 ha1, mul_nonneg ha1 ha2, mul_nonneg ha0 ha2,
    mul_nonneg (show 0 ≤ x^2 by positivity) (show 0 ≤ y^2 by positivity),
    mul_nonneg (show 0 ≤ x^4 by positivity) (show 0 ≤ y^4 by positivity),
    mul_nonneg (show 0 ≤ (x * y)^2 by positivity) (show 0 ≤ (x - y)^2 by positivity)]