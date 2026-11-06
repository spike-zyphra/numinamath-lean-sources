import Mathlib

theorem algebra_312666 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a + b > c) (h₄ : a + c > b) (h₅ : b + c > a) :
    ¬∃ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by 
  rintro ⟨x, h_eq⟩
  have h_eq : b ^ 2 * x ^ 2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by 
    linarith

  have h7 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 - 4 * b ^ 2 * c ^ 2 < (0 : ℝ) := by
    have h8 : (b + c - a) > 0 := by linarith
    have h9 : (b + c + a) > 0 := by linarith
    have h9' : (b + c - a) * (b + c + a) > 0 := by nlinarith 
    have h10 : (b - c) ^ 2 < (a) ^ 2 := by
      nlinarith 
    nlinarith [show (b + c - a) * (b + c + a) > 0 by nlinarith, 
      sq_nonneg (b^2 + c^2 - a^2 - 2 * b * c), sq_nonneg (b - c), 
      sq_pos_of_pos (show 0 < b by linarith), sq_pos_of_pos (show 0 < c by linarith), 
      mul_pos h₁ h₂, mul_pos h₀ h₂, mul_pos h₀ h₁ 
      ]
  
  have h8 : False := by 
    have h9 : b ^ 2 * x ^ 2 + (b^2 + c^2 - a^2) * x + c ^ 2 = 0 := h_eq
    have h10 : b^2 > 0 := by nlinarith
    have h11 : b ^ 2 * x ^ 2 + (b^2 + c^2 - a^2) * x + c ^ 2 = b ^ 2 * (x + (b^2 + c^2 - a^2) / (2 * b^2)) ^ 2 - ((b^2 + c^2 - a^2) ^ 2 - 4 * b ^ 2 * c ^ 2) / (4 * b ^ 2) := by
      field_simp
      ring_nf
    rw [h11] at h9 
    have h12 : b ^ 2 * (x + (b^2 + c^2 - a^2) / (2 * b^2)) ^ 2 ≥ (0 : ℝ) := by
      have h15 : b^2 ≥ (0 : ℝ) := by nlinarith
      have h16 : (x + (b^2 + c^2 - a^2) / (2 * b^2)) ^ 2 ≥ (0 : ℝ) := by
        apply sq_nonneg
      nlinarith [show b^2 ≥ 0 by nlinarith, show (x + (b^2 + c^2 - a^2) / (2 * b^2)) ^ 2 ≥ 0 by apply sq_nonneg]
    have h14 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 - 4 * b ^ 2 * c ^ 2 < (0 : ℝ) := h7
    have h15 : ((b ^ 2 + c ^ 2 - a^2) ^2 - 4 * b ^ 2 * c ^ 2) / (4 * b ^2 ) < (0 : ℝ) := by
      apply div_neg_of_neg_of_pos
      · -- Show (b^2 + c^2 - a^2)^2 - 4 * b^2 * c^2 < 0
        linarith
      · -- Show 4 * b^2 > 0
        nlinarith
    have eq1 : b ^ 2 * (x + (b^2 + c^2 - a^2) / (2 * b^2)) ^ 2 = ((b ^ 2 + c ^ 2 - a ^ 2) ^2 - 4 * b ^ 2 * c ^ 2) / (4 * b ^ 2 ) := by
      linarith [h9]
    nlinarith [eq1, h12, h15]
  exact h8