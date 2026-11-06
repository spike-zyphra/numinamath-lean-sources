import Mathlib

theorem algebra_11710 (r : ℝ) (hr : r ≠ 2 ∧ r ≠ -1) :
    (r + 3) / (r - 2) = (r - 1) / (r + 1) ↔ r = -1 / 7 := by 
  constructor
  · -- Assume $\frac{r+3}{r-2} = \frac{r-1}{r+1}$, prove $r = -\frac{1}{7}$
    intro h
    have h1 : r - 2 ≠ 0 := by
      intro h2
      apply hr.1
      linarith
    have h2 : r + 1 ≠ 0 := by
      intro h3
      apply hr.2
      linarith
    field_simp [h1, h2] at h 
    have h3 : r = -1 / 7 := by
      nlinarith
    exact h3
  · -- Assume r = -1/7, prove $\frac{r+3}{r-2} = \frac{r-1}{r+1}$
    intro h 
    have h1 : r - 2 ≠ 0 := by
      intro h2
      apply hr.1
      linarith
    have h2 : r + 1 ≠ 0 := by
      intro h3
      apply hr.2
      linarith
    rw [h] 
    norm_num