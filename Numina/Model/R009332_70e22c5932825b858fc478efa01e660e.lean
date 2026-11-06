import Mathlib

theorem algebra_92954 {a b : ℝ} (ha : a = 150 / 100 * b) (hb : b ≠ 0) :
(3 * b) / a = 200 / 100 := by
  have ha2 : a ≠ 0 := by
    intro h
    rw [ha] at h
    have : b = 0 := by
      linarith
    contradiction

  rw [ha]
  field_simp [hb]
  ring_nf