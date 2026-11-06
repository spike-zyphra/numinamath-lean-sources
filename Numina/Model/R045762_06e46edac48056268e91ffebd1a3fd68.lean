import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_322230 (u : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, u x y = y^2 - 2 * y + x^2 + 4 * x) :
  IsLeast {z | ∃ x y, z = u x y ∧ 2 * x + y ≥ 1} (-9 / 5) := by
  constructor 
  · -- Show $-9/5$ is in the set.
    use -2 / 5, 9 / 5 
    constructor 
    · -- Verify $u(-2/5, 9/5) = -9/5$.
      rw [h₀ (-2 / 5) (9 / 5)]
      norm_num 
    · -- Verify $2 * (-2/5) + 9/5 \geq 1$.
      norm_num 
  · -- Show $-9/5$ is the least.
    intro z hz 
    rcases hz with ⟨x, y, h_eq, h_ineq⟩ 
    rw [h₀ x y] at h_eq 
    nlinarith [sq_nonneg (x + 2 / 5), sq_nonneg (y - 9 / 5), sq_nonneg (2 * x + y - 1)]