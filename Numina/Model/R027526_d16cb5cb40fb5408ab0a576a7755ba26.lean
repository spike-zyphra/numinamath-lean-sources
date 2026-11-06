import Mathlib

theorem algebra_216467 (t r : ℝ) (ht : t > 0) (hr : r > 0)
    (h : r = 15 * t) (h' : 1000 / r = 1000 / t + 100 / 15) :
    t * 100 = 940 := by
  rw [h] at h'
  have eq7 : 1000 = 1000 * 15 + 100 * t := by
    have h1 : t > 0 := ht
    have h2 : 15 * t > 0 := by nlinarith
    have eq8 : 1000 / (15 * t) = 1000 / t + 100 / 15 := h'
    have eq9 : 1000 / (15 * t) * (15 * t) = (1000 / t + 100 / 15) * (15 * t) := by
      rw [eq8]
    have eq10 : 1000 / (15 * t) * (15 * t) = 1000 := by
      have hx2 : (15 * t) ≠ 0 := by nlinarith
      field_simp [hx2]
      <;> ring
    have eq11 : (1000 / t + 100 / 15) * (15 * t) = 15000 + 100 * t := by
      have eq12 : (1000 / t + 100 / 15) * (15 * t) = (1000 / t) * (15 * t) + (100 / 15) * (15 * t) := by ring
      rw [eq12]
      have eq14 : (1000 / t) * (15 * t) = 15000 := by
        have h6 : t ≠ 0 := by linarith
        field_simp [h6]
        <;> ring
      have eq15 : (100 / 15) * (15 * t) = 100 * t := by 
        field_simp at *
        <;> ring
      rw [eq14, eq15]
      <;> ring_nf
    linarith [eq10, eq11]
  nlinarith