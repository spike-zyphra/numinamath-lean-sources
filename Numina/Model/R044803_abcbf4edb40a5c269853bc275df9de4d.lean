import Mathlib

theorem algebra_253578 {x : ℝ} (hx : x ≠ 1 ∧ x > 0)(y : ℝ) (hy : y = 1 / x) :
    ∃ a b c, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + c^2 = b^2 ∧
      a = |x - y| / 2 ∧ b = (x + y) / 2 ∧ c = x * y := by
  have hx1 : x ≠ 1 := hx.left
  have hx2 : x > 0 := hx.right
  use |x - y| / 2, (x + y) / 2, x * y
  have hx3 : x ≠ (0 : ℝ) := by linarith
  have hy1 : y = 1 / x := hy
  constructor
  · -- Show that a > 0
    have hneq : x - y ≠ 0 := by
      by_contra h'
      have h_eq : x = y := by linarith
      rw [show y = 1 / x by linarith [hy]] at h_eq
      have h1 : x^2 = 1 := by
        field_simp [hx3] at h_eq
        nlinarith
      have h2 : x = 1 ∨ x = -1 := by
        have h2 : x^2 - 1 = 0 := by linarith
        have h3 : (x - 1) * (x + 1) = 0 := by nlinarith [h2]
        cases (mul_eq_zero.1 h3) with
        | inl h4 => 
          left
          linarith
        | inr h5 => 
          right
          linarith
      cases h2 with
      | inl h3 => 
        have h4 : x = 1 := by linarith
        tauto
      | inr h4 => 
        linarith
    have hx4 : |x - y| > 0 := by
      apply abs_pos.mpr
      intro h'
      apply hneq
      linarith
    have hx5 : |x - y| / 2 > 0 := by
      linarith [hx4]
    linarith
  constructor
  · -- Show that b > 0
    have hy_pos : y > 0 := by
      rw [hy]
      apply one_div_pos.mpr
      linarith
    have hx_sum_pos : x + y > 0 := by
      linarith
    linarith
  constructor
  · -- Show that c > 0
    have hx_pos : x > 0 := hx2
    have hy_pos : y > 0 := by
      rw [hy]
      apply one_div_pos.mpr
      linarith
    have hx_mul_y_pos : x * y > 0 := by
      nlinarith
    linarith
  constructor
  · -- Show that a^2 + c^2 = b^2
    have hy11 : y = 1 / x := hy
    have hx4 : x ≠ (0 : ℝ) := hx3
    have h1 : x * y = 1 := by 
      rw [hy11]
      field_simp [hx4]
    have hx5 : (|x - y| / 2) ^ 2 + (x * y) ^ 2 = ((x + y) / 2) ^ 2 := by
      have h11 : x * y = 1 := h1
      have h12 : (|x - y| / 2) ^ 2 + (x * y) ^ 2 = ((|x - y|) ^ 2) / 4 + (1 : ℝ) := by
        nlinarith [h11]
      have h13 : ((x + y) / 2) ^ 2 = ((x + y) ^ 2) / 4 := by ring
      rw [h12, h13]
      have h14 : (|x - y|) ^ 2 = (x - y) ^ 2 := by
        rw [sq_abs]
      rw [h14]
      have h2 : (x - y) ^ 2 + 4 = (x + y) ^ 2 := by
        have h15 : x * y = 1 := h1
        nlinarith [h15]
      field_simp at *
      nlinarith
    nlinarith [hx5]
  constructor
  · -- Show that a = |x - y| / 2
    rfl
  constructor
  · -- Show that b = (x + y) / 2
    rfl
  · -- Show that c = x * y
    rfl