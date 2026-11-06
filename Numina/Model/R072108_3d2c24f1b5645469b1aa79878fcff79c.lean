import Mathlib

open Real Set

theorem inequalities_132923 (x : ℝ) :
    ∃ y : ℝ, |x + y| + |x + 1| + |y + 1| = 2 ↔
    x = -1 := by 
  use (-x - 2)
  constructor
  · -- Forward direction: equation implies x = -1
    intro h
    have h1 : |x + (-x - 2)| + |x + 1| + |-x - 2 + 1| = 2 := by
      linarith
    have h2 : |x + (-x - 2)| = 2 := by 
      have h3 : x + (-x - 2) = -2 := by ring
      rw [h3]
      norm_num
    have h4 : |-x - 2 + 1| = |x + 1| := by
      have h5 : -x - 2 + 1 = -(x + 1) := by ring
      rw [h5]
      rw [abs_neg]
    rw [h2, h4] at h1
    have h3 : |x + 1| = 0 := by
      nlinarith
    have h4 : x + 1 = 0 := by
      rwa [abs_eq_zero] at h3
    linarith
  · -- Backward direction: x = -1 implies equation
    intro h
    rw [h]
    norm_num [abs_of_nonneg, abs_of_nonpos]
    <;> ring_nf <;> norm_num