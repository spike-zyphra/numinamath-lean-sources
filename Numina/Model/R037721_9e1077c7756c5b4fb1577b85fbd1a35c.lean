import Mathlib
namespace Algebra_611064

theorem Algebra_611064 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ^ 2 = x * y) :
  (x ≥ 4) ∧ (y = 2 → x = 4) := by

  have h1 : y^2 - x * y + x = 0 := by nlinarith

  have h2 : x ^ 2 - 4 * x ≥ 0 := by 
    nlinarith [sq_nonneg (y - x / 2), sq_nonneg (y), sq_nonneg (y - 2), sq_nonneg (x - 4), mul_pos hx hy, sq_nonneg ((y - 2) * (y + 0)), mul_pos hx (show 0 < (y : ℝ) by linarith), mul_pos hy (show 0 < (x : ℝ) by linarith)]

  have h3 : x ≥ 4 := by 
    nlinarith

  constructor
  · -- Show that x ≥ 4
    exact h3 
  · -- Show that if y = 2, then x = 4 
    intro hy_eq
    rw [hy_eq] at hxy 
    nlinarith