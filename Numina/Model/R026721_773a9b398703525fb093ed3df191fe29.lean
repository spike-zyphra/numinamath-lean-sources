import Mathlib

theorem algebra_174987 (v : ℝ) (h : v > 0) (h1 : 80 / v = 2 * (80 / (v + w))) (h2 : 2 * (80 / (v + w)) = 2 * (80 / v) + 30 / 60) :
    w = 64 := by
  have h3 : v ≠ 0 := by linarith
  have h4 : v + w ≠ 0 := by
    by_contra h4
    have : w = -v := by linarith
    rw [this] at h1
    field_simp [h3] at h1
    <;> nlinarith
  have h5 : 80 * (v + w) = 160 * v := by
    have eq1 : 80 / v = 2 * (80 / (v + w)) := h1
    have eq2 : 80 / v = 160 / (v + w) := by
      rw [eq1]
      ring
    have h6 : v ≠ 0 := h3
    have h7 : v + w ≠ 0 := h4
    field_simp [h6, h7] at eq2 ⊢
    nlinarith [h, sq_pos_of_pos h]
  have hw : w = v := by
    nlinarith
  have hw_eq : v + w = 2 * v := by
    linarith [hw]
  rw [show v + w = 2 * v by linarith [hw_eq]] at h2
  -- Simplify h2
  have h6 : 80 / v = 160 / v + (30 / 60 : ℝ) := by
    field_simp [(show (2 * v : ℝ) ≠ 0 by
      by_contra h7
      have : v = 0 := by linarith
      linarith [h3]
    ), h3] at h2 ⊢
    nlinarith [h2]
  -- From h6 derive h7
  have h7 : -80 / v = (30 / 60 : ℝ) := by
    have eq3 : 80 / v = 160 / v + (30 / 60 : ℝ) := h6
    have eq4 : 80 / v - (160 / v) = (30 / 60 : ℝ) := by linarith
    have eq5 : 80 / v - (160 / v) = -80 / v := by
      field_simp [h3]
      <;> ring_nf <;> field_simp [h3]
      <;> ring
    linarith [eq5, eq4]
  -- From h7 derive h8
  have h8 : -80 = (30 / 60 : ℝ) * v := by
    have h9 : v ≠ 0 := h3
    have h10 : -80 / v = (30 / 60 : ℝ) := h7
    have h11 : -80 / v * v = (30 / 60 : ℝ) * v := by
      rw [h10]
    have h12 : -80 / v * v = -80 := by
      field_simp [h9]
      <;> linarith
    linarith [h11, h12]
  have h9 : v = -160 := by
    nlinarith
  linarith