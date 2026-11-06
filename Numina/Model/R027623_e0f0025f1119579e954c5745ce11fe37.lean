import Mathlib

theorem algebra_108144 (f : ℝ → ℝ) (a b c : ℝ) (h₀ : ∀ x, f x = x ^ 3 - 2 * x ^ 2 - 3 * x + 4)
    (h₁ : f a = f b) (h₂ : f b = f c) (h₃ : a < b) (h₄ : b < c) :
    a ^ 2 + b ^ 2 + c ^ 2 = 10 := by
  have h1' : a ^ 3 - 2 * a ^ 2 - 3 * a + 4 = b ^ 3 - 2 * b ^ 2 - 3 * b + 4 := by
    rw [h₀ a] at h₁
    rw [h₀ b] at h₁
    linarith

  have eq1 : a ^ 2 + a * b + b ^ 2 - 2 * (a + b) - 3 = 0 := by 
    have h1'' : a ^ 3 - 2 * a ^ 2 - 3 * a + 4 = b ^ 3 - 2 * b ^ 2 - 3 * b + 4 := h1'
    have h6 : a ^ 3 - 2 * a ^ 2 - 3 * a = b ^ 3 - 2 * b ^ 2 - 3 * b := by linarith 
    have h7 : a ^ 3 - b ^ 3 - 2 * (a ^ 2 - b ^ 2) - 3 * (a - b) = 0 := by 
      nlinarith 
    have h9 : a - b < 0 := by linarith 
    have h10 : a ^ 3 - b ^ 3 - 2 * (a ^ 2 - b ^ 2) - 3 * (a - b) = (a - b) * (a ^ 2 + a * b + b ^ 2 - 2 * (a + b) - 3) := by 
      ring 
    rw [h10] at h7 
    have h11 : a - b ≠ 0 := by linarith 
    have eq1 : a ^ 2 + a * b + b ^ 2 - 2 * (a + b) - 3 = 0 := by 
      apply (mul_left_inj' h11).mp 
      linarith 
    linarith

  have h2' : b ^ 3 - 2 * b ^ 2 - 3 * b + 4 = c ^ 3 - 2 * c ^ 2 - 3 * c + 4 := by
    rw [h₀ b] at h₂
    rw [h₀ c] at h₂
    linarith

  have eq2 : b ^ 2 + b * c + c ^ 2 - 2 * (b + c) - 3 = 0 := by 
    have h2'' : b ^ 3 - 2 * b ^ 2 - 3 * b + 4 = c ^ 3 - 2 * c ^ 2 - 3 * c + 4 := h2'
    have h7 : b ^ 3 - 2 * b ^ 2 - 3 * b = c ^ 3 - 2 * c ^ 2 - 3 * c := by linarith 
    have h8 : b ^ 3 - c ^ 3 - 2 * (b ^ 2 - c ^ 2) - 3 * (b - c) = 0 := by 
      nlinarith 
    have h9 : b - c < 0 := by linarith 
    have h10 : b ^ 3 - c ^ 3 - 2 * (b ^ 2 - c ^ 2) - 3 * (b - c) = (b - c) * (b ^ 2 + b * c + c ^ 2 - 2 * (b + c) - 3) := by 
      ring 
    rw [h10] at h8 
    have h11 : b - c ≠ 0 := by linarith 
    have eq2 : b ^ 2 + b * c + c ^ 2 - 2 * (b + c) - 3 = 0 := by 
      apply (mul_left_inj' h11).mp 
      linarith 
    linarith

  -- Subtracting eq2 - eq1, we get:
  -- \( (c - a)(a + b + c - 2) = 0 \)
  have eq3 : (c - a) * (a + b + c - 2) = 0 := by 
    nlinarith
  -- Since \( A < c \), so \( A - c \neq 0 \), so \( a + b + c - 2 = 0 \)
  have eq4 : a + b + c - 2 = 0 := by 
    have h7 : c - a > 0 := by linarith
    cases' (mul_eq_zero.mp eq3) with h6 h8 
    · -- case h6 : c - a = 0 
      nlinarith 
    · -- case h8 : a + b + c - 2 = 0 
      linarith 
  have h7 : a + b + c = 2 := by linarith 
  nlinarith [sq_pos_of_pos (sub_pos.mpr h₃), sq_pos_of_pos (sub_pos.mpr h₄), sq_pos_of_pos (sub_pos.mpr (by linarith : a < c)), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]