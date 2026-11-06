import Mathlib

open Real Set
open scoped Real

theorem algebra_198890 {θ : ℝ} (a : ℝ) (ha : a = cos θ ^ 4 - sin θ ^ 4 - 2 * cos θ ^ 2) :
    a = -1 := by
  rw [ha]
  have h1 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq θ
  have h2 : cos θ ^ 4 - sin θ ^ 4 = cos θ ^ 2 - sin θ ^ 2 := by
    calc
      cos θ ^ 4 - sin θ ^ 4
        = (cos θ ^ 2) ^ 2 - (sin θ ^ 2) ^ 2 := by ring
      _ = (cos θ ^ 2 - sin θ ^ 2) * (cos θ ^ 2 + sin θ ^ 2) := by
        ring_nf
      _ = (cos θ ^ 2 - sin θ ^ 2) * 1 := by
        have h3 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
          linarith [h1]
        rw [h3]
        all_goals nlinarith
      _ = cos θ ^ 2 - sin θ ^ 2 := by
        ring_nf
  calc
    cos θ ^ 4 - sin θ ^ 4 - 2 * cos θ ^ 2
        = (cos θ ^ 4 - sin θ ^ 4) - 2 * cos θ ^ 2 := by ring
    _ = (cos θ ^ 2 - sin θ ^ 2) - 2 * cos θ ^ 2 := by
      rw [h2]
    _ = cos θ ^ 2 - sin θ ^ 2 - 2 * cos θ ^ 2 := by ring
    _ = - (sin θ ^ 2 + cos θ ^ 2) := by ring
    _ = - (1) := by
      have h3 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
        linarith [h1]
      rw [h3]
      all_goals nlinarith
    _ = -1 := by ring