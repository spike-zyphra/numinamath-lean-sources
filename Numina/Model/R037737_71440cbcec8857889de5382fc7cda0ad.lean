import Mathlib

theorem algebra_123329 (a : ℕ → ℝ) (h₀ : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h₁ : a 9 = 13) (h₂ : a 13 = 1) :
    Real.logb (a 1) 13 = 1 / 3 := by
  rcases h₀ with ⟨r, hr⟩
  have h₃ : a 9 = a 0 * r ^ 9 := hr 9
  have h₄ : a 13 = a 0 * r ^ 13 := hr 13
  rw [h₃] at h₁ 
  rw [h₄] at h₂ 
  have h₅ : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    norm_num at hr ⊢
    linarith
  have h₆ : r ^ 4 = 1 / 13 := by
    have h₇ : a 0 * r ^ 13 = (a 0 * r ^ 9) * r ^ 4 := by
      ring
    rw [show a 0 * r ^ 9 = 13 by linarith] at h₇
    linarith
  have h₈ : a 1 = 13 ^ 3 := by
    have h₉ : a 0 * r ^ 9 = 13 := by linarith
    have h₁₀ : r ^ 4 = 1 / 13 := h₆
    have h₁₁ : a 1 = a 0 * r := by 
      rw [h₅]
      all_goals ring
    have h₁₂ : r ^ 8 = (1 / 13) ^ 2 := by
      calc 
        r ^ 8 = (r ^ 4) ^ 2 := by ring
        _ = (1 / 13) ^ 2 := by rw [h₆]
    have h₁₃ : a 0 * r ^ 9 = (a 0 * r) * r ^ 8 := by 
      ring_nf
    rw [show a 0 * r = a 1 by linarith [h₅, h₁₁]] at h₁₃
    rw [h₁₂] at h₁₃
    have h₁₄ : a 1 = 13 ^ 3 := by 
      field_simp at h₁₃ ⊢
      nlinarith
    linarith
  rw [h₈]
  have h₉ : Real.logb (13 ^ 3) 13 = 1 / 3 := by 
    rw [Real.logb]
    have h10 : Real.log (13 ^ 3) = 3 * Real.log 13 := by 
      simp [Real.log_pow]
      <;> ring 
    rw [h10]
    have h11 : Real.log 13 ≠ 0 := by 
      have h12 : Real.log 13 > 0 := by 
        apply Real.log_pos
        all_goals norm_num
      linarith 
    field_simp [h11]
    <;> nlinarith 
  linarith