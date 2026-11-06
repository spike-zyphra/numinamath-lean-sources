import Mathlib

theorem algebra_196418 (v : ℝ) (h : v > 0) (h1 : 90 / (v + w) = 70 / (v - w)) :
    w * 90 / (v + w) = 10 := by
  have h2 : v - w ≠ 0 := by
    by_contra h3
    have h4 : v = w := by linarith
    rw [show v - w = 0 by linarith [h4] ] at h1
    field_simp [(show v + w ≠ 0 by
      by_contra h5
      have h6 : v = -w := by linarith
      nlinarith
    )] at h1
    <;> nlinarith
  have h3 : v + w ≠ 0 := by
    by_contra h4
    have h5 : v = -w := by linarith
    rw [show v + w = 0 by linarith [h5] ] at h1
    field_simp [(show v - w ≠ 0 by
      by_contra h6
      have h7 : v = w := by linarith
      nlinarith [show w ≥ 0 by nlinarith]
    )] at h1
    <;> nlinarith
  have h4 : 90 * (v - w) = 70 * (v + w) := by
    have h5 : v + w ≠ 0 := h3
    have h6 : v - w ≠ 0 := h2
    field_simp [h5, h6] at h1 ⊢
    nlinarith
  have h5 : v = 8 * w := by
    nlinarith
  have hw : w ≠ 0 := by
    by_contra hw0
    have h7 : w = 0 := by linarith
    have h8 : v = 0 := by
      rw [show w = 0 by linarith [h7] ] at h5
      linarith
    linarith
  have h6 : v + w = 9 * w := by
    rw [h5]
    ring
  have hwne : 9 * w ≠ 0 := by
    intro h9
    have hw0 : w = 0 := by
      linarith
    contradiction
  rw [show v + w = 9 * w by linarith [h6] ]
  field_simp [hwne, hw]
  <;> nlinarith