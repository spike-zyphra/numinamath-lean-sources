import Mathlib

theorem algebra_13552 (x : ℝ) (h : Real.sin x + Real.cos x = Real.sqrt 7 / 2) :
    (Real.sin x)^3 + (Real.cos x)^3 = 5 * Real.sqrt 7 / 16 := by

  have h₁ : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h₂ : Real.sin x * Real.cos x = 3 / 8 := by
    have h₂ : Real.sin x + Real.cos x = Real.sqrt 7 / 2 := h
    have h₃ : (Real.sin x + Real.cos x) ^ 2 = (Real.sqrt 7 / 2) ^ 2 := by
      rw [h₂]
    have h₄ : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by ring
    have h₅ : (Real.sqrt 7 / 2) ^ 2 = 7 / 4 := by
      calc
        (Real.sqrt 7 / 2) ^ 2 = (Real.sqrt 7) ^ 2 / 4 := by ring
        _ = 7 / 4 := by rw [Real.sq_sqrt (by norm_num)]; all_goals norm_num
    rw [h₄] at h₃
    rw [h₅] at h₃
    rw [h₁] at h₃
    linarith

  have h₄ : (Real.sin x) ^ 3 + (Real.cos x) ^ 3 = (Real.sin x + Real.cos x) * ((Real.sin x ^ 2 + Real.cos x ^ 2) - (Real.sin x * Real.cos x)) := by
    ring

  rw [h₄, h₁, h₂, h]
  ring_nf
  <;> field_simp
  <;> ring_nf <;> norm_num <;> ring