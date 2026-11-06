import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_278225 (f : ℝ → ℝ) (hf : f = λ x => x^4 - 3 * x^2 + 2) :
    IsLeast {x | ∃ y, f y = x} (-1 / 4) := by
  constructor
  · -- Show $-1/4$ is achievable by finding a specific input.
    use Real.sqrt 6 / 2
    rw [hf]
    have h1 : (Real.sqrt 6 / 2: ℝ) ^ 2 = 3 / 2 := by
      calc
        (Real.sqrt 6 / 2: ℝ) ^ 2 = (Real.sqrt 6) ^ 2 / 4 := by ring_nf
        _ = 6 / 4 := by rw [Real.sq_sqrt]; all_goals norm_num
        _ = 3 / 2 := by norm_num
    have h2 : (Real.sqrt 6 / 2: ℝ) ^ 4 = 9 / 4 := by
      calc
        (Real.sqrt 6 / 2: ℝ) ^ 4 = ((Real.sqrt 6 / 2) ^ 2) ^ 2 := by ring
        _ = (3 / 2) ^ 2 := by rw [h1]
        _ = 9 / 4 := by norm_num
    simp only [h1, h2]
    norm_num
  · -- Show $-1/4$ is indeed the least value
    intro x hx
    rcases hx with ⟨y, hy⟩
    rw [hf] at hy
    simp at hy
    nlinarith [sq_nonneg (y^2 - 3 / 2), sq_nonneg (y^2), sq_nonneg ((y^2) - 3 / 2), sq_nonneg ((y^2) * (y^2)), sq_nonneg ((y^2) - (3 / 2)), sq_nonneg (y^2), sq_nonneg (y * 2)]