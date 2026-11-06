import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_71844 (x y z : ℝ) (hx : x ∈ Icc 1 4) (hy : y ∈ Icc 1 4) (hz : z ∈ Icc 1 4)
  (h : x - y + z = 4) :
  10 * (1/4 * x^2 - 1/5 * y^2 + 1/6 * z^2) ≥ 23 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  have hz' : z = 4 - x + y := by linarith
  rw [hz']
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x - y - 1),
          sq_nonneg ((4 - x + y) - 3),
          mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 - 1) (by linarith : (0 : ℝ) ≤ x - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - x) (by linarith : (0 : ℝ) ≤ 4 - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - 1) (by linarith : (0 : ℝ) ≤ y - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - y) (by linarith : (0 : ℝ) ≤ 4 - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) (by linarith : (0 : ℝ) ≤ y - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) (by linarith : (0 : ℝ) ≤ (4 - x + y) - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ y - 1) (by linarith : (0 : ℝ) ≤ (4 - x + y) - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) (by linarith : (0 : ℝ) ≤ 4 - x),
          mul_nonneg (by linarith : (0 : ℝ) ≤ y - 1) (by linarith : (0 : ℝ) ≤ 4 - y)
]