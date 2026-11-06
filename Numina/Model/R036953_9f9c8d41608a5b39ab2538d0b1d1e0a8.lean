import Mathlib

theorem algebra_292494 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + b + c = 1 / a) (h2 : b^2 + c + a = 1 / b) (h3 : c^2 + a + b = 1 / c) :
    a = b ∨ a = c ∨ b = c := by

  have eq1 : a^3 + a * b + a * c = 1 := by
    have h := h1
    field_simp [ha] at h ⊢
    linarith [h]
  
  have eq2 : b^3 + b * c + b * a = 1 := by
    have h := h2
    field_simp [hb] at h ⊢
    linarith [h]
  
  have eq3 : c^3 + c * a + c * b = 1 := by
    have h := h3
    field_simp [hc] at h ⊢
    linarith [h]

  have eq4 : (a - b) * (a^2 + a * b + b^2 + c) = 0 := by
    nlinarith [eq1, eq2]

  have eq5 : (b - c) * (b^2 + b * c + c^2 + a) = 0 := by
    nlinarith [eq2, eq3]

  by_cases h4 : a - b = 0
  · -- If a - b = 0, then a = b
    left
    linarith
  · -- Assume a - b ≠ 0, then from eq4 we get a^2 + ab + b^2 + c = 0
    have eq6 : a^2 + a * b + b^2 + c = 0 := by
      apply (mul_left_inj' (show a - b ≠ 0 by exact h4)).mp
      linarith
    by_cases h5 : b - c = 0
    · -- If b - c = 0, then b = c
      right
      right
      linarith
    · -- Assume b - c ≠ 0, then from eq5 we get b^2 + b * c + c^2 + a = 0
      have eq7 : b^2 + b * c + c^2 + a = 0 := by
        apply (mul_left_inj' (show b - c ≠ 0 by exact h5)).mp
        linarith
      have eq8 : (a - c) * (a + b + c - 1) = 0 := by
        nlinarith [eq6, eq7]
      cases' (mul_eq_zero.mp eq8) with h9 h10
      · -- If a - c = 0, then a = c
        right
        left
        linarith
      · -- If a + b + c = 1
        have h11 : a + b + c = 1 := by linarith
        have h12 : (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 = 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
            h11, eq1, eq2, eq3, eq6, eq7]
        have h13 : a - b = 0 := by 
          nlinarith [h12, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
        exfalso
        apply h4
        linarith