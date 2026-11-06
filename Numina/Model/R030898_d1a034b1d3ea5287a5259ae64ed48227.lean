import Mathlib

theorem algebra_226516 :
    {(a, b) : ℝ × ℝ | a * b = 1 ∧ (a + b + 2) / 4 = 1 / (a + 1) + 1 / (b + 1) ∧ 
    a ≠ -1 ∧ b ≠ -1} = {(1, 1)} := by
  ext ⟨a, b⟩
  simp [-one_div]
  constructor
  · -- Assume (a, b) is in the set.
    rintro ⟨h1, h2, ha, hb⟩
    have h3 : a + b + 2 ≠ 0 := by
      by_contra h
      have h4 : a + b = -2 := by linarith
      have h5 : a * b = 1 := h1
      have h6 : (a + 1) * (b + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- a + 1 = 0
        exfalso
        apply ha
        linarith
      · -- b + 1 = 0
        exfalso
        apply hb
        linarith
    have h4 : (a + 1) * (b + 1) = 4 := by
      have h5 : a + 1 ≠ 0 := by
        intro h
        apply ha
        linarith
      have h6 : b + 1 ≠ 0 := by
        intro h
        apply hb
        linarith
      field_simp [h5, h6] at h2 ⊢
      apply (mul_left_inj' h3).mp
      nlinarith [h2]
    have h5 : a + b = 2 := by
      nlinarith [h1, h4]
    have ha1 : a = 1 := by
      have h5' : a + b = 2 := h5
      have h1' : a * b = 1 := h1
      have h6 : b = 2 - a := by linarith
      rw [h6] at h1'
      have h7 : a ^ 2 - 2 * a + 1 = 0 := by
        nlinarith
      have h8 : (a - 1) ^ 2 = 0 := by
        nlinarith
      have h9 : a - 1 = 0 := by
        apply pow_eq_zero 
        exact h8
      linarith
    have hb1 : b = 1 := by
      linarith [h5, ha1]
    simp [ha1, hb1]
  · -- Show that (1, 1) is in the set.
    rintro ⟨rfl, rfl⟩
    constructor
    · -- a * b = 1
      norm_num
    constructor
    · -- (1 + 1 + 2) / 4 = 1 / (1 + 1) + 1 / (1 + 1)
      norm_num
    constructor
    · -- a ≠ -1
      norm_num
    · -- b ≠ -1
      norm_num