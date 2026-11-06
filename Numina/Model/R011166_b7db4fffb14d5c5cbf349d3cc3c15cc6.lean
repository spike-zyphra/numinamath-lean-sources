import Mathlib

theorem algebra_611338 :
    {(a, b, c) : ℝ × ℝ × ℝ | a < b ∧ b < c ∧ a + b + c = 21 / 4 ∧ 1 / a + 1 / b + 1 / c = 21 / 4 ∧ a * b * c = 1} = {(1 / 4, 1, 4)} := by

  ext ⟨a, b, c⟩
  simp [-one_div]
  constructor
  · -- Assume (a, b, c) in the set
    rintro ⟨h1, h2, h3, h4, h5⟩
    have eq1 : a ≠ 0 := by
      by_contra h
      rw [h] at h5
      nlinarith
    have eq2 : b ≠ 0 := by
      by_contra h
      rw [h] at h5
      nlinarith
    have eq3 : c ≠ 0 := by
      by_contra h
      rw [h] at h5
      nlinarith
    have eq4 : a * b + a * c + b * c = 21 / 4 := by
      field_simp [eq1, eq2, eq3] at h4
      nlinarith
    have h6 : (a - 1 / 4) * (a - 1) * (a - 4) = 0 := by
      nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (a - 1), sq_nonneg (a - 4), sq_nonneg (b - 1), sq_nonneg (c - 4), sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num), sq_nonneg (a * b - 1 / 4 * 1), sq_nonneg (a * c - 1 / 4 * 4), sq_nonneg (b * c - 1 * 4)]
    cases' (mul_eq_zero.mp h6) with h7 h8
    cases' (mul_eq_zero.mp h7) with h7 h9
    · -- Case a = 1/4
      have ha : a = 1 / 4 := by linarith
      have h10 : b + c = 5 := by
        nlinarith
      have h11 : b * c = 4 := by
        rw [ha] at h5
        nlinarith
      have ha1 : b = 1 := by
        nlinarith [sq_nonneg (b - 1), sq_nonneg (c - 4), sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num), h10, h11, h2]
      have ha2 : c = 4 := by
        nlinarith
      simp [ha, ha1, ha2]
    · -- Case a = 1
      have ha : a = 1 := by linarith
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (b - 4), sq_nonneg (c - 4)]
    · -- Case a = 4
      have ha : a = 4 := by linarith
      nlinarith [sq_nonneg (b - 1), sq_nonneg (c - 4), sq_nonneg (a - 4)]
  · -- Show that (1/4, 1, 4) is in the set
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Show 1/4 < 1
      norm_num
    constructor
    · -- Show 1 < 4
      norm_num
    constructor
    · -- Show 1/4 + 1 + 4 = 21/4
      norm_num
    constructor
    · -- Show 1/(1/4) + 1/1 + 1/4 = 21/4
      norm_num
    · -- Show (1/4) * 1 * 4 = 1
      norm_num