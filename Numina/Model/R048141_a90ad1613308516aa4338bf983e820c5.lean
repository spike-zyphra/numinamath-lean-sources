import Mathlib

theorem algebra_598886 {b : ℝ} (h : ∃ x, 1988*x^2+b*x+8891=0 ∧ 8891*x^2+b*x+1988=0) :
    b=10879 ∨ b=-10879 := by 
  rcases h with ⟨x, h₁, h₂⟩

  have h3 : 8891 * x^2 + b * x + 1988 - (1988 * x^2 + b * x + 8891) = 0 := by linarith
  have h4 : 6903 * x^2 - 6903 = 0 := by
    linarith

  have h5 : x^2 = 1 := by
    linarith

  have h6 : x = 1 ∨ x = -1 := by
    rw [sq_eq_one_iff] at h5
    tauto

  cases h6 with
  | inl h7 =>
    rw [h7] at h₁
    have hb : b = -10879 := by 
      linarith
    right
    linarith
  | inr h8 =>
    rw [h8] at h₁
    have hb : b = 10879 := by
      linarith
    left
    linarith