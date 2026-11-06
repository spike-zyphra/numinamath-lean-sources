import Mathlib

theorem algebra_10449 (l w : ℝ) (hl : l > 0) (hw : w > 0)
    (h : 2 * (l + w) = 40) :
    l * w ≤ 100 := by
        have h1 : l + w = 20 := by
            linarith
        have h2 : l * w ≤ ((l + w) / 2) ^ 2 := by
            nlinarith [sq_nonneg (l - w)]
        rw [h1] at h2
        nlinarith