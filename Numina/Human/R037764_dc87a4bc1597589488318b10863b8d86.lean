import Mathlib

/- Find all real numbers $a, b, c, d$ such that $a+b+c+d=20$ and $a b+a c+a d+b c+b d+c d=$ 150 .-/
theorem algebra_604648 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a + b + c + d = 20 ∧ a * b + a * c + a * d + b * c + b * d + c * d = 150} =
  {(5, 5, 5, 5)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  -- We first verify that (5, 5, 5, 5) is a solution.
  swap
  . rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num
  -- Let (a, b, c, d) be a solution.
  . rintro ⟨h₁, h₂⟩
    -- We can get (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2 = 0 from the given conditions.
    have h₃ : (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2 = 0 := by linear_combination (3 * a + 3 * b + 3 * c + 3 * d + 60) * h₁ - 8 * h₂
    -- Because all terms are non-negative, we have (a - b) ^ 2 = 0 = (a - c) ^ 2 = (a - d) ^ 2 = 0
    -- So we have a = b = c = d.
    have ⟨k₁, k₂, k₃⟩ : a = b ∧ a = c ∧ a = d := by
      refine ⟨?_, ?_, ?_⟩
      all_goals
        rw [← sub_eq_zero]
        apply pow_eq_zero (n := 2)
        linarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), h₃]
    -- Trivial.
    subst b c d
    simp
    linarith only [h₁]
