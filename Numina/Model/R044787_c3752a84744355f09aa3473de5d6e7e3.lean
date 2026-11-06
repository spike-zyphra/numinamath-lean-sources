import Mathlib

theorem algebra_222761 {x : ℝ} (hx : Real.tan x + 1 / Real.tan x = -2) (hxp : ¬∃ k : ℤ, x = k * Real.pi / 2) :
    (Real.sin x - Real.cos x)^10 = 32 := by

  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at hx

  have h1 : Real.sin x ≠ 0 := by
    by_contra h
    have h3 : Real.sin x = 0 := by linarith 
    have h4 : ∃ k : ℤ, x = k * Real.pi / 2 := by 
      have h5 : Real.sin x = 0 := by linarith 
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h5
      use 2 * k 
      field_simp at hk ⊢ 
      <;> linarith 
    contradiction

  have h2 : Real.cos x ≠ 0 := by
    by_contra h
    have h4 : Real.cos x = 0 := by linarith 
    have h5 : ∃ k : ℤ, x = k * Real.pi / 2 := by 
      have h6 : Real.cos x = 0 := by linarith 
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h6 
      use 2 * k + 1 
      field_simp at hk ⊢ 
      <;> linarith 
    contradiction

  have h3 : Real.sin x * Real.cos x = -1 / 2 := by 
    field_simp [h1, h2] at hx 
    nlinarith [Real.sin_sq_add_cos_sq x]

  have h4 : (Real.sin x - Real.cos x) ^ 2 = 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h3]

  calc 
    (Real.sin x - Real.cos x) ^ 10 = ((Real.sin x - Real.cos x) ^ 2) ^ 5 := by ring 
    _ = (2) ^ 5 := by rw [h4]
    _ = 32 := by norm_num