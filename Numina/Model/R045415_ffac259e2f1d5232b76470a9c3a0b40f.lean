import Mathlib

theorem algebra_235312
  (a b : Fin 4 → ℝ)
  (h₀ : a 0 * b 0 + a 1 * b 2 = 1)
  (h₁ : a 0 * b 1 + a 1 * b 3 = 0)
  (h₂ : a 2 * b 0 + a 3 * b 2 = 0)
  (h₃ : a 2 * b 1 + a 3 * b 3 = 1)
  (h₄ : a 1 * b 2 = 7) :
  a 3 * b 3 = -6 := by
  have h₅ : a 0 * b 0 = -6 := by
    nlinarith [h₀, h₄]

  have ha0_ne : a 0 ≠ 0 := by
    by_contra ha00
    rw [ha00] at h₅
    norm_num at h₅
    all_goals nlinarith
  have hb0_ne : b 0 ≠ 0 := by
    by_contra hb00
    rw [hb00] at h₅
    norm_num at h₅
    all_goals nlinarith
  have ha1_ne : a 1 ≠ 0 := by
    by_contra ha10
    rw [ha10] at h₄
    norm_num at h₄
    all_goals nlinarith
  have hb2_ne : b 2 ≠ 0 := by
    by_contra hb20
    rw [hb20] at h₄
    norm_num at h₄
    all_goals nlinarith
  
  have h₆ : a 2 = -a 3 * b 2 / b 0 := by
    have eq1 : a 2 * b 0 + a 3 * b 2 = 0 := by
      linarith [h₂]
    field_simp at *
    nlinarith
  
  have h₇ : b 1 = -a 1 * b 3 / a 0 := by
    have eq1 : a 0 * b 1 + a 1 * b 3 = 0 := by
      linarith [h₁]
    field_simp at *
    nlinarith
  
  have h₈ : a 3 * b 3 = -6 := by
    have eq1 : a 2 * b 1 + a 3 * b 3 = 1 := by
      linarith [h₃]
    rw [show a 2 = -a 3 * b 2 / b 0 by exact h₆, 
        show b 1 = -a 1 * b 3 / a 0 by exact h₇] at eq1
    field_simp at *
    nlinarith [sq_pos_of_ne_zero ha1_ne, sq_pos_of_ne_zero hb2_ne]

  linarith [h₈]