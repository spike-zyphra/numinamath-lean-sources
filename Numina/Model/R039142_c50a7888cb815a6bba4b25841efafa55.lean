import Mathlib


theorem algebra_22086 : {(a, c) : ℝ × ℝ | a ≠ 0 ∧ (∃! x : ℝ, a * x ^ 2 + 32 * x + c = 0) ∧ a + c = 130 ∧ a > c} = {(128, 2)} := by
  ext ⟨a, c⟩
  simp [-zero_ne_one]
  constructor
  · -- First, show that (a, c) in the set implies (a, c) = (128, 2)
    rintro ⟨ha_ne_zero, ⟨x, ⟨h_eq, h1⟩⟩, h_eq1, h2⟩

    have h_eq2 : ∀ (y : ℝ), a * y ^ 2 + 32 * y + c = 0 → y = x := by
      intro y hy
      apply h1 y
      all_goals
        try tauto

    have h_eq3 : a * (-32 / a - x) ^ 2 + 32 * (-32 / a - x) + c = 0 := by
      have eq1 : a * (-32 / a - x) ^ 2 + 32 * (-32 / a - x) + c = a * x ^ 2 + 32 * x + c := by
        have h3 : a ≠ 0 := ha_ne_zero
        field_simp [h3]
        ring
      rw [eq1]
      linarith [h_eq]

    have h_eq4 : -32 / a - x = x := by
      apply h_eq2 (-32 / a - x)
      exact h_eq3

    have h_eq5 : x = -16 / a := by
      field_simp [ha_ne_zero] at h_eq4 ⊢
      nlinarith

    have h_eq6 : a * x ^ 2 + 32 * x + c = 0 := h_eq

    rw [h_eq5] at h_eq6

    have h_eq8 : a * c = 256 := by
      have h3 : a ≠ 0 := ha_ne_zero
      have eq1 : a * (-16 / a) ^ 2 + 32 * (-16 / a) + c = 0 := by
        linarith
      have eq2 : a * (-16 / a) ^ 2 + 32 * (-16 / a) + c = c - 256 / a := by
        field_simp [ha_ne_zero]
        ring
      rw [eq2] at eq1
      have h3 : c - 256 / a = 0 := by linarith
      have h4 : a * (c - 256 / a) = 0 := by
        have h3' : c - 256 / a = 0 := by linarith
        rw [h3']
        norm_num
      have h5 : a * (c - 256 / a) = a * c - 256 := by
        field_simp [ha_ne_zero]
        all_goals
          ring
      rw [h5] at h4
      linarith

    have h_eq9 : a + c = 130 := h_eq1

    have h_eq11 : c = 130 - a := by linarith

    rw [h_eq11] at h_eq8

    have h_eq12 : a ^ 2 - 130 * a + 256 = 0 := by
      nlinarith

    have h_eq13 : (a - 128) * (a - 2) = 0 := by
      nlinarith

    cases' (mul_eq_zero.mp h_eq13) with h_eq14 h_eq15

    · -- a = 128
      have ha128 : a = 128 := by linarith

      have hc2 : c = 2 := by
        linarith [ha128, h_eq11]

      simp [ha128, hc2]

    · -- a = 2
      have ha2 : a = 2 := by linarith

      have hc128 : c = 128 := by
        nlinarith [ha2, h_eq11]

      nlinarith [ha2, hc128, h2]

  · -- Show that (128, 2) is in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · -- a ≠ 0
      norm_num
    constructor
    · -- Show that there exists a unique solution
      use -1 / 8
      constructor
      · -- Check that it's a solution
        norm_num
      · -- Show that it's unique
        intro y hy
        have h_eq : (128 : ℝ) * y ^ 2 + 32 * y + 2 = 0 := by linarith
        have h_eq2 : (y + 1 / 8) ^ 2 = 0 := by
          nlinarith
        have h_eq3 : y + 1 / 8 = 0 := by
          nlinarith
        linarith
    constructor
    · -- a + c = 130
      norm_num
    · -- a > c
      norm_num