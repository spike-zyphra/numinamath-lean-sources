import Mathlib

theorem algebra_95360 {a b c p q r x : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hx : 0 < x)
    (h : Real.logb 10 a / p = Real.logb 10 b / q) (h' : Real.logb 10 b / q = Real.logb 10 c / r)
    (h'' : Real.logb 10 c / r = Real.logb 10 x) (h''' : b ^ 2 / (a * c) = x ^ y) :
    y = 2 * q - p - r := by

  have hpne : p ≠ 0 := by linarith
  have hqne : q ≠ 0 := by linarith
  have hrne : r ≠ 0 := by linarith

  have h1 : Real.logb 10 a = p * Real.logb 10 x := by
    have h14 : Real.logb 10 a / p = Real.logb 10 x := by
      have h12 : Real.logb 10 a / p = Real.logb 10 c / r := by
        have h13 : Real.logb 10 a / p = Real.logb 10 b / q := h
        have h14 : Real.logb 10 b / q = Real.logb 10 c / r := h'
        linarith
      have h13 : Real.logb 10 c / r = Real.logb 10 x := h''
      linarith
    have : Real.logb 10 a = p * Real.logb 10 x := by
      field_simp [hpne] at h14 ⊢
      linarith
    assumption

  have h2 : Real.logb 10 b = q * Real.logb 10 x := by
    have h14 : Real.logb 10 b / q = Real.logb 10 x := by
      have h12 : Real.logb 10 b / q = Real.logb 10 c / r := h'
      have h13 : Real.logb 10 c / r = Real.logb 10 x := h''
      linarith
    have : Real.logb 10 b = q * Real.logb 10 x := by
      field_simp [hqne] at h14 ⊢
      linarith
    assumption

  have h3 : Real.logb 10 c = r * Real.logb 10 x := by
    have h14 : Real.logb 10 c / r = Real.logb 10 x := h''
    have : Real.logb 10 c = r * Real.logb 10 x := by
      field_simp [hrne] at h14 ⊢
      linarith
    assumption

  have h4 : Real.logb 10 (b ^ 2 / (a * c)) = (2 * q - p - r) * Real.logb 10 x := by
    have h5 : Real.logb 10 (b ^ 2 / (a * c)) = Real.logb 10 (b ^ 2) - Real.logb 10 (a * c) := by
      rw [Real.logb_div (by
        have hb1 : 0 < b := by linarith [hb.left]
        have : 0 < b ^ 2 := by positivity
        positivity
      ) (by
        have ha1 : 0 < a := by linarith [ha.left]
        have hc1 : 0 < c := by linarith [hc.left]
        positivity
      )]

    have h6 : Real.logb 10 (b ^ 2) = 2 * Real.logb 10 b := by
      simp [Real.logb_pow]

    have h7 : Real.logb 10 (a * c) = Real.logb 10 a + Real.logb 10 c := by
      rw [Real.logb_mul (by linarith [ha.left]) (by linarith [hc.left])]

    rw [h5, h6, h7]
    rw [h1, h2, h3]
    all_goals ring

  have h40 : Real.logb 10 (b ^ 2 / (a * c)) = Real.logb 10 (x ^ y) := by
    rw [h''']

  have h41 : Real.logb 10 (x ^ y) = y * Real.logb 10 x := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  rw [h41] at h40
  rw [h4] at h40

  have hx1 : Real.logb 10 x ≠ 0 := by
    by_contra h15
    have h16 : Real.logb 10 x = 0 := by linarith
    have hx10 : x = 1 := by
      have : x = 1 := by
        have h100 : Real.logb 10 x = 0 := h16
        rw [Real.logb_eq_iff_rpow_eq] at h100
        · linarith
        all_goals linarith
      assumption

    have h160 : Real.logb 10 a = 0 := by
      rw [h1]
      rw [h16]
      norm_num

    have ha10 : a = 1 := by
      have : a = 1 := by
        have h100 : Real.logb 10 a = 0 := h160
        rw [Real.logb_eq_iff_rpow_eq] at h100
        · linarith
        all_goals linarith
      assumption

    have hne1 : a ≠ 1 := ha.right
    contradiction

  have h42 : y = 2 * q - p - r := by
    apply (mul_left_inj' hx1).mp
    linarith

  linarith