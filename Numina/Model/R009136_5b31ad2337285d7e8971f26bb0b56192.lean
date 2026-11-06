import Mathlib

theorem algebra_12955 {s l a : ℝ}
    (hpos : 0 < l ∧ 0 < s ∧ 0 < a)
    (h0 : s < l)
    (h1 : (l - a) = 0.1 * a)
    (h2 : (a - s) = 0.1 * a) :
    s * l / a ^ 2 = 99 / 100 := by
  have ha_pos : 0 < a := hpos.right.right
  have h3 : l = 1.1 * a := by
    linarith
  have h4 : s = 0.9 * a := by
    nlinarith
  have h5 : s * l = 0.99 * a^2 := by
    rw [h3, h4]
    ring_nf
  have h6 : a^2 ≠ 0 := by
    nlinarith
  rw [h5]
  -- Now we have to calculate (0.99 * a^2) / a^2 = 99 / 100
  field_simp [h6]
  <;> ring_nf <;> field_simp [h6] <;> linarith