import Mathlib

theorem algebra_15116 {x : ℝ} (hx : x ≠ -10) (hx' : x ≠ -6) :
    1 / (x + 9) + 1 / (x + 7) = 1 / (x + 10) + 1 / (x + 6) ↔ x = -8 := by

  constructor
  · -- Assume $\frac{1}{x + 9} + \frac{1}{x + 7} = \frac{1}{x + 10} + \frac{1}{x + 6}$ prove $x = -8$
    intro h
    have h1 : x + 10 ≠ 0 := by
      intro h2
      apply hx
      linarith

    have h2 : x + 6 ≠ 0 := by
      intro h3
      apply hx'
      linarith

    have h3 : x + 9 ≠ 0 := by
      by_contra h4
      have : x = -9 := by linarith
      rw [this] at h
      norm_num at h
      <;> linarith

    have h4 : x + 7 ≠ 0 := by
      by_contra h5
      have : x = -7 := by linarith
      rw [this] at h
      norm_num at h
      <;> linarith

    field_simp [(show x + 9 ≠ 0 by assumption), (show x + 7 ≠ 0 by assumption), (show x + 10 ≠ 0 by assumption), (show x + 6 ≠ 0 by assumption)] at h

    have h_eq : x + 8 = 0 := by
      ring_nf at h ⊢
      nlinarith [sq_nonneg (x + 8)]

    have hx_eq : x = -8 := by linarith
    exact hx_eq

  · -- Assume x = -8 prove the equation
    intro h_eq
    rw [h_eq]
    norm_num
    <;> linarith