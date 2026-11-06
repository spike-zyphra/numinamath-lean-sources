import Mathlib

theorem algebra_219936 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (n / 2) * (8 / 9 : ℚ) = n - 1) :
    n = 72 := by
  have h₂ : (n : ℚ) > 0 := by
    have h₃ : n > 0 := by
      by_contra h
      push_neg at h
      have : n = 0 := by
        omega
      contradiction 
    exact_mod_cast h₃
  -- Multiply both sides by 9 to clear denominators
  have h₃ : (n : ℚ) * 4 = 9 * (n : ℚ) - 9 := by 
    field_simp at h₁
    nlinarith
  have h₄ : (n : ℚ) = 9 / 5 := by 
    nlinarith
  have h₈ : (n * 5 : ℚ) = 9 := by 
    rw [show (n : ℚ) = 9 / 5 by linarith [h₄]]
    norm_num
  have h₉ : (n * 5) = 9 := by 
    exact_mod_cast h₈ 
  omega