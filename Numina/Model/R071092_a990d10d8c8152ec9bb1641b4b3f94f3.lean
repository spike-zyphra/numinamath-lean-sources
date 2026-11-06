import Mathlib

theorem algebra_297800 {a b c : ℝ} (ha : a + b + c = 0) (hb : a^3 + b^3 + c^3 = 0) :
    a^19 + b^19 + c^19 = 0 := by
  have h1 : a * b * c = 0 := by
    have h4 : a^3 + b^3 + c^3 = 3 * a * b * c := by
      have h5 : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a*b + b*c + c*a)) := by
        ring
      rw [ha] at h5
      have h6 : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by linarith
      linarith
    rw [hb] at h4
    linarith

  cases' (mul_eq_zero.mp h1) with h2 h3
  cases' (mul_eq_zero.mp h2) with ha1 hb1

  · -- Case where a = 0
    have ha0 : a = 0 := ha1
    have hc0 : c = -b := by
      linarith
    rw [ha0, hc0]
    ring_nf

  · -- Case where b = 0
    have hb0 : b = 0 := hb1
    have hc1 : c = -a := by
      linarith
    rw [hb0, hc1]
    ring_nf

  · -- Case where c = 0
    have hc0 : c = 0 := h3
    have hb2 : b = -a := by
      linarith
    rw [hc0, hb2]
    ring_nf