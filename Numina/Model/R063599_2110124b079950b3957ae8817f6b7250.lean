import Mathlib

theorem algebra_10497 {q r s t : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hqr : q / r = 9) (hps : s / r = 6) (hst : s / t = 1 / 2) : t / q = 4 / 3 := by
  -- From q/r = 9, get q = 9r
  have h1 : q = 9 * r := by
    have h := hqr
    field_simp [hr] at h
    nlinarith
  -- From s/r = 6, get s = 6r
  have h2 : s = 6 * r := by
    have h := hps
    field_simp [hr] at h
    nlinarith
  -- From s /t = 1/2, get s = (1/2) * t
  have h3 : s = (1 / 2) * t := by
    have h := hst
    field_simp [ht] at h
    nlinarith
  -- Substitute s into s = (1/2)t to get t = 2s
  have ht_eq : t = 2 * s := by
    nlinarith
  -- Substitute s = 6r into t = 2s to get t = 12r
  have ht_in_r : t = 12 * r := by
    rw [ht_eq]
    rw [h2]
    ring
  -- Now compute t/q
  -- t = 12 r and q = 9 r, so t / q = 12 / 9 = 4 / 3
  have h4 : t / q = 4 / 3 := by
    have h5 : q ≠ 0 := by
      by_contra h6
      rw [h6] at h1
      have : r = 0 := by linarith
      contradiction
    field_simp [h5]
    nlinarith [ht_in_r, h1, hr]
  exact h4