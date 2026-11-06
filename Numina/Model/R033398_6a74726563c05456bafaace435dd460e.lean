import Mathlib

theorem algebra_607159 {a b : ℝ} (h : 2 * a + a ^ 2 = 2 * b + b ^ 2) (ha : ∃ m : ℤ, a = m) :
    ∃ n : ℤ, b = n := by
  rcases ha with ⟨m, rfl⟩
  have h1 : (m : ℝ) ^ 2 + 2 * (m : ℝ) = (b ^ 2 + 2 * b) := by linarith
  have h2 : ( (m : ℝ) + 1 ) ^ 2 = ( b + 1 ) ^ 2 := by nlinarith
  have h3 : ( (m : ℝ) + 1 ) = ( b + 1 ) ∨ ( (m : ℝ) + 1 ) = - ( b + 1 ) := by
    have h4 : ( (m : ℝ) + 1 ) ^ 2 - ( b + 1 ) ^ 2 = 0 := by
      nlinarith
    have h5 : ( (m : ℝ) + 1 + (b + 1 ) ) * ( (m : ℝ) + 1 - ( b + 1 ) ) = 0 := by
      nlinarith
    cases' ( mul_eq_zero.mp h5 ) with h6 h7
    · -- Case ( (m + 1 ) + (b + 1 ) ) * ( ... ) = 0
      right
      nlinarith
    · -- Case ... * ( (m + 1 ) - (b + 1 ) ) = 0
      left
      linarith
  cases h3 with
  | inl h_eq =>
    -- In this case, b = m
    have : b = (m : ℝ) := by
      nlinarith
    refine ⟨m, by simp [this]⟩
  | inr h_eq =>
    -- In this case, b = -m - 2
    have : b = ( - (m : ℝ) - 2 ) := by
      nlinarith
    refine ⟨-m - 2, by
      rw [ this ]
      all_goals norm_num
      all_goals norm_num
    ⟩