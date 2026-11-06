import Mathlib

/- Sure, here is the translated text:

Solve the following equation and verify the solution by substitution:
( x(x + 3)− 4{3 − [5x − (1 − 2x)] - ((x − 1) ^ 2) / 4 ) / (−4x/3 − {−1−[5/2 *(x + 6/5) − x] + x/6 }) = x/2 * (x + 6)−{−x[−3(x − 4) + 2(3x − 5) − 10}
-/

theorem algebra_265750 (x : ℝ) :
    (x * (x + 3) - 4 * (3 - (5 * x - (1 - 2 * x)) - ((x - 1) ^ 2) / 4)) /
    (- 4 * x / 3 - (- 1 - ((5 / 2) * (x + 6 / 5) - x) + (x / 6))) =
    x / 2 * (x + 6) - (-x * (-3 * (x - 4) + 2 * (3 * x - 5) - 10)) ↔
    x = 15 / 4 ∨ x = 1 / 3 := by 
  constructor
  all_goals intro h
  --on the LHS set A as the numerator, B the denominator; and set the RHS as C
  · let A := x * (x + 3) - 4 * (3 - (5 * x - (1 - 2 * x)) - ((x - 1) ^ 2) / 4)
    let B := - 4 * x / 3 - (- 1 - ((5 / 2) * (x + 6 / 5) - x) + (x / 6))
    let C := x / 2 * (x + 6) - (-x * (-3 * (x - 4) + 2 * (3 * x - 5) - 10))
    --by solving the linear arithmetic, we get that A = 2 * x ^ 2 + 29 * x - 15, B = 4, C = 7 / 2 * x ^ 2 - 5 * x
    have hA : A = 2 * x ^ 2 + 29 * x - 15 := by simp[A]; ring_nf
    have hB : B = 4 := by simp[B]; field_simp; ring_nf
    have hC : C = 7 / 2 * x ^ 2 - 5 * x := by simp[C]; ring_nf
    --substituting back in the original euqation, we get a quadratic equation which we solve to get as solutions 15/4 and 1/3
    have heq' : (2 * x ^ 2 + 29 * x - 15) / 4 = 7 / 2 * x ^ 2 - 5 * x := by 
      rw[← hA, ← hB, ← hC]
      simp[A,B,C]
      simp at h
      exact h
    have sqeq : (x - 15 / 4) * (x - 1/ 3) = 0 := by 
      ring_nf
      linarith
    rw[mul_eq_zero] at sqeq
    obtain x1|x2 := sqeq
    · left
      linarith
    · right
      linarith
  --of course, substituting both 15/4 and 1/3 in the original equation and than solving via arithmetic yields 0 = 0. 
  · obtain x1|x2 := h
    · rw[x1]
      ring_nf
    · rw[x2]
      ring_nf