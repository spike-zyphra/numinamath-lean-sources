import Mathlib

theorem algebra_199187 (x : ℝ) (hx : x ≠ 49 ∧ x ≠ 50) :
    (x - 49) / 50 + (x - 50) / 49 = 49 / (x - 50) + 50 / (x - 49) ↔
    x = 0 ∨ x = 99 ∨ x = 4901 / 99 := by
  constructor
  · -- Forward: If the equation holds, prove the disjunction
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : x - 49 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : x - 50 ≠ 0 := by
      intro h3
      apply hx2
      linarith
    field_simp [h1, h2] at h
    have h3 : (x - 0) * (x - 99) * (x - 4901 / 99) = 0 := by
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 99), sq_nonneg (x - 4901 / 99),
        sq_pos_of_ne_zero (show x - 49 ≠ 0 by
          intro h2
          apply hx1
          linarith
        ), sq_pos_of_ne_zero (show x - 50 ≠ 0 by
          intro h3
          apply hx2
          linarith
        )
      ]
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    · -- x = 0
      left
      linarith
    · -- x - 99 = 0
      right
      left
      linarith
    · -- x - 4901/99 = 0
      right
      right
      linarith
  · -- Backward: Assume the disjunction, prove the equation
    rintro (h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 99
      rw [h]
      norm_num
    · -- x = 4901/99
      rw [h]
      norm_num