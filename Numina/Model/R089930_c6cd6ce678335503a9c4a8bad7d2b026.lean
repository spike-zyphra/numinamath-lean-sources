import Mathlib

theorem number_theory_304563 (x : ℝ) (hx : x < -2) : y = abs (1 - abs (1 + x)) ↔ y = -2 - x := by
  constructor
  · -- Assume y = abs (1 - abs (1 + x)), prove y = -2 - x
    intro h
    rw [h]
    have h1 : abs (1 + x) = - (1 + x) := by
      rw [abs_of_neg]
      linarith
    have h2 : abs (1 - abs (1 + x)) = abs (2 + x) := by
      rw [h1]
      ring_nf
      <;> ring_nf <;> norm_num
      <;> ring
    have h3 : abs (2 + x) = - (2 + x) := by
      rw [abs_of_neg]
      linarith
    rw [h2, h3]
    all_goals linarith
  · -- Assume y = -2 - x, prove y = abs (1 - abs (1 + x))
    intro h
    rw [h]
    have h1 : abs (1 + x) = - (1 + x) := by
      rw [abs_of_neg]
      linarith
    have h2 : abs (1 - abs (1 + x)) = abs (2 + x) := by
      rw [h1]
      ring_nf
      <;> ring_nf <;> norm_num
      <;> ring
    have h3 : abs (2 + x) = - (2 + x) := by
      rw [abs_of_neg]
      linarith
    rw [h2, h3]
    all_goals linarith