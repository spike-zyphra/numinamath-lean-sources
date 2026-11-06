import Mathlib

theorem algebra_2624 : {x : ℝ | (abs (x^2 - 1) - x * abs (x + 1)) = 0} = {-1, 1/2} := by
  ext x
  simp
  constructor
  · intro h
    by_cases h1 : x ≥ 1
    · -- In this case, x^2 - 1 ≥ 0 and x + 1 > 0
      rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)] at h
      have : x = -1 := by nlinarith
      left
      linarith

    by_cases h2 : 0 ≤ x
    · by_cases h2' : x < 1
      · -- In this case, x^2 - 1 < 0 and x + 1 ≥ 0
        rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)] at h
        have h_eq : 2 * x^2 + x - 1 = 0 := by
          nlinarith
        have h3 : (x - 1 / 2) * (2 * x + 2) = 0 := by
          ring_nf at h_eq ⊢
          linarith
        cases' (mul_eq_zero.mp h3) with h4 h5
        · -- x = 1/2 is valid
          right
          linarith
        · -- x = -1 contradicts 0 ≤ x < 1
          linarith

      · -- x ≥ 1 and x ≥ 0 ( improbable )
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)] at h
        have : x = -1 := by nlinarith
        linarith

    by_cases h3 : -1 ≤ x
    · by_cases h3' : x < 0
      · -- In this case, x^2 - 1 ≤ 0 and x + 1 ≥ 0
        rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)] at h
        have h_eq : 2 * x^2 + x - 1 = 0 := by
          nlinarith
        have h6 : (x - 1 / 2) * (2 * x + 2) = 0 := by
          ring_nf at h_eq ⊢
          linarith
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- x = 1/2 contradicts -1 ≤ x < 0
          linarith
        · -- x = -1 is valid
          left
          linarith

      · -- x ≥ 0 contradicts -1 ≤ x < 0
        linarith

    · -- x < -1
      rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)] at h
      have h_eq : 2 * x^2 + x - 1 = 0 := by
        nlinarith
      have h9 : (x - 1 / 2) * (2 * x + 2) = 0 := by
        ring_nf at h_eq ⊢
        linarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- x = 1/2 contradicts x < -1
        linarith
      · -- x = -1 is valid
        left
        linarith
  · rintro (hx | hx)
      <;> rw [hx]
      <;> field_simp at *
    norm_num
    rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by norm_num)]
    linarith
