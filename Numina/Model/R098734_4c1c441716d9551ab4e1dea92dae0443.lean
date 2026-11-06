import Mathlib

theorem algebra_10258 (a r : ℤ) (h₀ : 0 < a) (h₁ : 0 < r) (h₂ : a = 2) (h₃ : a * r ^ 4 = 162) :
    a * r ^ 5 = 486 := by
  rw [h₂] at h₃
  have h4 : r ^ 4 = 81 := by
    nlinarith
  have hr : r = 3 := by
    have h5 : r ^ 4 = 81 := h4
    have h6 : r ≤ 3 := by
      by_contra h
      push_neg at h
      have h7 : r ≥ 4 := by omega
      have h8 : r ^ 4 ≥ 256 := by
        have h9 : r ≥ 4 := h7
        have h10 : r ^ 4 ≥ (4 : ℤ) ^ 4 := by
          apply pow_le_pow_left
          all_goals nlinarith
        have h11 : (4 : ℤ) ^ 4 = 256 := by
          norm_num
        linarith
      nlinarith
    interval_cases r <;> omega
  rw [h₂, hr]
  norm_num