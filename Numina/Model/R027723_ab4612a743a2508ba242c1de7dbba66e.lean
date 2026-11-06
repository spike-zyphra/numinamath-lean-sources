import Mathlib

theorem algebra_1414 (x : ℝ) (hx : x ≠ 1) (hx' : x ≠ -1) :
    1 / (x - 1) + 1 / (x + 1) + 2 * x / (x ^ 2 + 1) + 4 * x ^ 3 / (x ^ 4 + 1) =
    8 * x ^ 7 / (x ^ 8 - 1) := by

  have h1 : x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have h2 : x + 1 ≠ 0 := by
    intro h
    apply hx'
    linarith
  have h3 : x ^ 2 + 1 ≠ 0 := by
    by_contra h
    have h8 : x ^ 2 = -1 := by linarith
    nlinarith [sq_nonneg x]

  have h4 : x ^ 4 + 1 ≠ 0 := by
    by_contra h
    have h9 : x ^ 4 = -1 := by linarith
    nlinarith [sq_nonneg (x ^ 2 )]

  have h5 : x ^ 8 - 1 ≠ 0 := by
    by_contra h6
    have h7 : (x - 1) * (x + 1) * (x ^ 2 + 1) * (x ^ 4 + 1) = 0 := by
      nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 ), sq_nonneg (x + 1), sq_nonneg (x - 1) ]
    cases' (mul_eq_zero.mp h7) with h73 h74
    cases' (mul_eq_zero.mp h73) with h75 h76
    cases' (mul_eq_zero.mp h75) with h77 h78
    · -- Case x - 1 = 0
      have h3 : x = 1 := by linarith
      tauto
    · -- Case x + 1 = 0
      have h3 : x = -1 := by linarith
      tauto
    · -- Case x ^ 2 + 1 = 0
      exfalso
      exact h3 (by linarith)
    · -- Case x ^ 4 + 1 = 0
      exfalso
      have h8 : x ^ 4 + 1 = 0 := by
        nlinarith
      nlinarith [sq_nonneg (x ^ 2 ), sq_nonneg x, h4, h3, h1, h2, h4]

  field_simp [(show x - 1 ≠ 0 by exact h1), (show x + 1 ≠ 0 by exact h2), (show x ^ 2 + 1 ≠ 0 by exact h3), (show x ^ 4 + 1 ≠ 0 by exact h4), (show x ^ 8 - 1 ≠ 0 by exact h5)]
  <;> ring_nf