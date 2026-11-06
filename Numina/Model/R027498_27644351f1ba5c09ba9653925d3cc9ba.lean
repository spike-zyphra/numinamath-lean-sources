import Mathlib

theorem algebra_188191 (x : ℝ) (hx : x ≠ -8 ∧ x ≠ -9 ∧ x ≠ -15 ∧ x ≠ -6) :
    (2 / (x + 8)) + (5 / (x + 9)) = (3 / (x + 15)) + (4 / (x + 6)) ↔
    x = 6 ∨ x = -33 / 4 := by
  constructor
  · -- Assume the equation holds, prove $x = 6 \vee x = -33/4$.
    intro h
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    have h1 : x + 8 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : x + 9 ≠ 0 := by
      intro h3
      apply hx2
      linarith
    have h3 : x + 15 ≠ 0 := by
      intro h4
      apply hx3
      linarith
    have h4 : x + 6 ≠ 0 := by
      intro h5
      apply hx4
      linarith
    field_simp [h1, h2, h3, h4] at h
    have h5 : (x - 6) * (x + 33 / 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case $x - 6 = 0$
      left
      linarith
    · -- Case $x + \frac{33}{4} = 0$
      right
      linarith
  · -- Assume $x = 6 \vee x = -33/4$, prove the equation.
    rintro (h | h)
    · -- Case $x = 6$
      rw [h]
      norm_num
    · -- Case $x = -\frac{33}{4}$
      rw [h]
      norm_num