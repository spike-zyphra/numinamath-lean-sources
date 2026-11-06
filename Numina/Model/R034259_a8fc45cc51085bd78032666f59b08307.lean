import Mathlib

open Real

/- Given $x \ne 1$, if $\frac{x}{x-1} > 2$, find the range of $x$.

 -/
theorem inequalities_6580 (x : ℝ) (hx : x ≠ 1) (h : x / (x - 1) > 2) : 1 < x ∧ x < 2 := by

  have h1 : x - 1 ≠ 0 := by
    intro h2
    apply hx
    linarith

  have h_three : (x - 1) > 0 ∨ (x - 1) < 0 := by 
    have : x - 1 < 0 ∨ x - 1 > 0 := by 
      apply lt_or_gt_of_ne h1
    exact or_comm.mp this

  cases h_three with
  | inl h2 =>
    have h4 : 1 < x := by linarith

    have h5 : x / (x - 1) * (x - 1) > 2 * (x - 1) := by 
      apply mul_lt_mul_of_pos_right h h2

    have h6 : x < 2 := by
      have : x / (x - 1) * (x - 1) = x := by
        field_simp [h2]
      rw [this] at h5
      linarith

    exact ⟨h4, h6⟩

  | inr h2 => 
    have h5 : x / (x - 1) * (x - 1) < 2 * (x - 1) := by 
      apply mul_lt_mul_of_neg_right h h2

    have : x / (x - 1) * (x - 1) = x := by
      field_simp [show x - 1 ≠ 0 by intro h2'; apply h1; linarith]

    rw [this] at h5

    have h6 : x > 2 := by linarith

    have h4 : x < 1 := by linarith

    linarith -- contradiction