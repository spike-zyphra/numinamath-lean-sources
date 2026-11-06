import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

theorem inequalities_143624
    (x y z : ℝ)
    (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
    (h₁ : x + y + z = 1) :
    x * y + y * z + z * x ≤ 2 / 7 + 9 * x * y * z / 7 := by 
  have h2 : z = 1 - x - y := by linarith
  rw [h2]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg ((1 - x - y) - 1/3),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ (1 - x - y : ℝ) by nlinarith),
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ (1 - x - y : ℝ) by nlinarith)
        ]