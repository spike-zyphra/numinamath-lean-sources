import Mathlib

theorem algebra_11710 (r : ℝ) (hr : r ≠ 2 ∧ r ≠ -1) :
    (r + 3) / (r - 2) = (r - 1) / (r + 1) ↔ r = -1 / 7 := by
  constructor
  · -- First direction: (r + 3) / (r - 2) = (r - 1) / (r + 1) → r = -1 / 7
    intro h
    have h1 : r - 2 ≠ 0 := by intro h2; apply hr.left; linarith
    have h2 : r + 1 ≠ 0 := by intro h3; apply hr.right; linarith
    field_simp [(show r - 2 ≠ 0 by assumption), (show r + 1 ≠ 0 by assumption)] at h
    have : r ^ 2 + 4 * r + 3 = r ^ 2 - 3 * r + 2 := by linarith
    have : 7 * r = -1 := by linarith
    linarith
  · -- Second direction: r = -1 / 7 → (r + 3) / (r - 2) = (r - 1) / (r + 1)
    intro h
    rw [h]
    norm_num