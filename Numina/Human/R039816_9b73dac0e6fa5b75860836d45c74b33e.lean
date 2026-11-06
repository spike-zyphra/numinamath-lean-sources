import Mathlib

theorem algebra_22141 {a b c d : ℝ} (ha : a = 1) (hb : b = 4)
    (h1 : (b^2 - 4*a*d) / (b^2 - 4*a*c) = c / d)
    (h2 : c ≠ d) : c + d = 4 := by
  rw [ha, hb] at h1
  by_cases hd: d = 0
  · rw [hd] at h1
    simp at h1
    linarith
  simp at h1

  by_cases hc: (4 ^ 2 - 4 * c) = 0
  · rw [hc, show c = 4 by linarith, Eq.comm] at h1
    simp at h1
    linarith

  field_simp at h1
  have : 4 * (c + d) * (c - d) = 16 * (c - d) := by linarith
  simp at this

  obtain (r | r) := this
  · linarith
  · exact absurd (by linarith) h2
