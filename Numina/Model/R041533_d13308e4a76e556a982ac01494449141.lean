import Mathlib

theorem algebra_121877 (x : ℝ) (hx : x ≠ 0) :
    (∑ i ∈ Finset.range 15, x ^ i) / (x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x) =
    (x ^ 10 + x ^ 5 + 1) / x := by
  have h1 : (∑ i in Finset.range 15, x ^ i) =
    (x ^ 14 + x ^ 13 + x ^ 12 + x ^ 11 + x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h1]
  field_simp [(show x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x ≠ 0 by
    by_contra h
    have h3 : x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x = 0 := by linarith
    have h4 : x * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = 0 := by
      linarith [h3]
    cases (mul_eq_zero.1 h4) with
    | inl h5 => 
      exfalso
      apply hx
      linarith
    | inr h6 =>
      have h7 : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0 := by
        linarith
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1/2), sq_nonneg (x ^ 2 - 1)]
  ), hx]
  <;> ring