import Mathlib
theorem algebra_272908 (a b : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : b ≠ 0)
    (h₂ : ∃ x y, a * x + b * y = 2 ∧ x^2 / 6 + y^2 / 2 = 1) :
    a / b ≤ -1 ∨ a / b ≥ 1 := by 
  rcases h₂ with ⟨x, y, h₃, h₄⟩ 
  have h₅ : y = (2 - a * x) / b := by 
    have h₁' : b ≠ 0 := h₁ 
    field_simp 
    linarith 
  rw [h₅] at h₄ 
  have h₇ : x ^ 2 * b ^ 2 + 3 * (2 - a * x) ^ 2 = 6 * b ^ 2 := by 
    field_simp at h₄ ⊢ 
    nlinarith 
  have hb : b^2 + 3 * a ^ 2 ≥ 2 := by
    have h₈ : x ^ 2 * b ^ 2 + 3 * (2 - a * x) ^ 2 = 6 * b ^ 2 := h₇
    have h₉ : ( -12 * a ) ^ 2 - 4 * ( b ^ 2 + 3 * a ^ 2 ) * ( 12 - 6 * b ^ 2 ) ≥ 0 := by 
      nlinarith [ sq_nonneg ( x * ( b ^ 2 + 3 * a ^ 2 ) - 6 * a ) , sq_nonneg ( x - (6 * a ) / ( b ^ 2 + 3 * a ^ 2 ) ) , sq_nonneg ( ( -12 * a ) + 2 * ( b ^ 2 + 3 * a ^ 2 ) * x ) , sq_nonneg ( x * ( b ) ) , sq_nonneg ( a * b ) , h₀ , sq_nonneg ( x - 2 ) , sq_nonneg ( a - 0 ) , sq_nonneg ( b - 0 ) ]
    nlinarith 
  have h₁₃ : (a / b) ^ 2 ≥ 1 := by 
    have h₁₄ : b^2 > 0 := by
      exact sq_pos_of_ne_zero h₁ 
    have h₁₅ : (a / b) ^ 2 = a^2 / b^2 := by 
      field_simp [h₁] 
    rw [h₁₅] 
    apply (le_div_iff₀ (by positivity)).mpr 
    nlinarith [ h₀, hb ] 
  by_cases h : a / b ≥ 0 
  · -- If a/b ≥ 0, then a/b ≥ 1 
    have h₁₇ : a / b ≥ 1 := by 
      nlinarith [ h₁₃, h ]
    right 
    linarith 
  · -- else a/b < 0 
    have h₁₈ : a / b ≤ -1 := by 
      nlinarith [ h₁₃, show a / b ≤ 0 by linarith ] 
    left 
    linarith