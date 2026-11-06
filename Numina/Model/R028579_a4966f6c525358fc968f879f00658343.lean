import Mathlib

theorem algebra_222667 {w : ℂ} (hw : w^3 = 1) (h : w.im ≠ 0) :
    (1 - w + w^2) * (1 + w - w^2) = 4 := by

  have hw2 : w ^ 2 = -w - 1 := by
    have h1 : w^3 - 1 = 0 := by
      rw [hw]
      ring
    have h2 : (w - 1) * (w ^ 2 + w + 1) = 0 := by
      calc
        (w - 1) * (w ^ 2 + w + 1) = (w ^ 3 - 1) := by ring_nf
        _ = 0 := h1
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- If h2 : w - 1 = 0
      have h5 : w = 1 := by
        calc
          w = (w - 1) + 1 := by ring_nf
          _ = 0 + 1 := by rw [h3]
          _ = 1 := by ring_nf
      rw [h5] at h
      norm_num [Complex.ext_iff] at h
      all_goals
        try { tauto }
    · -- If h2 : w^2 + w + 1 = 0
      have h5 : w ^ 2 + w + 1 = 0 := h4
      calc
        w ^ 2 = (w ^ 2 + w + 1) - w - 1 := by ring_nf
        _ = 0 - w - 1 := by rw [h5]
        _ = -w - 1 := by ring_nf

  have hw4 : w^4 = w := by
    calc
      w^4 = w * w^3 := by ring_nf
      _ = w * 1 := by rw [hw]
      _ = w := by ring_nf

  calc
    (1 - w + w^2) * (1 + w - w^2)
        = 1 - w^2 + 2 * w^3 - w^4 := by
          ring_nf
    _ = 1 - (-w - 1) + 2 * 1 - w := by
      rw [hw2, hw, hw4]
    _ = 4 := by
      ring_nf