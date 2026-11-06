import Mathlib

theorem algebra_273857 {a b : ℝ} (ha : a = (2 / 3) * b) (hb : b ≠ 0) :
    (9 * a + 8 * b) / (6 * a) = 7 / 2 := by
  have ha1 : a ≠ 0 := by
    intro h
    have h1 : b = 0 := by
      rw [ha] at h
      nlinarith
    contradiction
  have num_eq : 9 * a + 8 * b = 14 * b := by
    rw [ha]
    linarith
  have denom_eq : 6 * a = 4 * b := by
    rw [ha]
    linarith
  rw [num_eq, denom_eq]
  have hb' : b ≠ 0 := hb
  field_simp [hb']
  <;> nlinarith