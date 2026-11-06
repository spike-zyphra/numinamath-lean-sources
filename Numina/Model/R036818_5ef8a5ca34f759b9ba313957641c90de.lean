import Mathlib

theorem algebra_247491 (a b c d : ℝ) (ha : 0 < a) (hroots : ∃ x y, x ≠ y ∧ x^2 + d * x + a = 0 ∧ y^2 + d * y + a = 0)
    (hroots' : ∃ x y, x ≠ y ∧ x^2 + c * x + b = 0 ∧ y^2 + c * y + b = 0) (hord : a < b ∧ b < c ∧ c < d) :
    ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ x^2 + d * x + a = 0 ∧ y^2 + d * y + a = 0 ∧
    z^2 + c * z + b = 0 ∧ w^2 + c * w + b = 0 := by
  rcases hroots with ⟨x, y, hxy1, heq1, heq2⟩
  rcases hroots' with ⟨z, w, hwz1, heq3, heq4⟩
  use x, y, z, w
  have h1 : x ≠ y := hxy1
  have h2 : z ≠ w := hwz1
  have h3 : x^2 + d * x + a = 0 := heq1
  have h4 : y^2 + d * y + a = 0 := heq2
  have h5 : z^2 + c * z + b = 0 := heq3
  have h6 : w^2 + c * w + b = 0 := heq4
  constructor
  · exact h1
  constructor
  · -- Show that x ≠ z
    by_contra h7
    have hz7 : z = x := by linarith
    rw [show z = x by linarith] at h5
    have h7' : x^2 + c * x + b = 0 := by
      linarith
    have hb : a < b := hord.1
    have hc : b < c := hord.2.1
    have hd : c < d := hord.2.2
    nlinarith [sq_nonneg (x + d / 2), sq_nonneg (x + c / 2), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hc) (sub_pos.mpr hd)]
  constructor
  · -- Show that x ≠ w
    by_contra h8
    have hw8 : w = x := by linarith
    rw [show w = x by linarith] at h6
    have h8' : x^2 + c * x + b = 0 := by
      linarith
    have hb : a < b := hord.1
    have hc : b < c := hord.2.1
    have hd : c < d := hord.2.2
    nlinarith [sq_nonneg (x + d / 2), sq_nonneg (x + c / 2), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hc) (sub_pos.mpr hd)]
  constructor
  · -- Show that y ≠ z
    by_contra h9
    have h9 : y = z := by linarith
    rw [show z = y by linarith] at h5
    have h9' : y^2 + c * y + b = 0 := by
      linarith
    have hb : a < b := hord.1
    have hc : b < c := hord.2.1
    have hd : c < d := hord.2.2
    nlinarith [sq_nonneg (y + d / 2), sq_nonneg (y + c / 2), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hc) (sub_pos.mpr hd)]
  constructor
  · -- Show that y ≠ w
    by_contra h10
    have h10 : y = w := by linarith
    rw [show w = y by linarith] at h6
    have h10' : y^2 + c * y + b = 0 := by
      linarith
    have hb : a < b := hord.1
    have hc : b < c := hord.2.1
    have hd : c < d := hord.2.2
    nlinarith [sq_nonneg (y + d / 2), sq_nonneg (y + c / 2), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hd), mul_pos (sub_pos.mpr hc) (sub_pos.mpr hd)]
  constructor
  · -- Show that z ≠ w
    exact h2
  constructor
  · exact h3
  constructor
  · exact h4
  constructor
  · exact h5
  · exact h6