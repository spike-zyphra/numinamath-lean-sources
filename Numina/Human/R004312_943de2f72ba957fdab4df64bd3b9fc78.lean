import Mathlib

/- Example 5. Solve the equation


$$

\sqrt{11 x+3}-\sqrt{2-x}-\sqrt{9 x+7}+\sqrt{x-2}=0

$$
 -/
theorem algebra_252027 (x : ℝ) (h1 : 0 ≤ 11 * x + 3) (h2 : 0 ≤ 2 - x ) (h3 : 0 ≤ 9 * x + 7) (h4 : 0 ≤ x - 2):
    Real.sqrt (11 * x + 3) - Real.sqrt (2 - x) = Real.sqrt (9 * x + 7) - Real.sqrt (x - 2) ↔ x = 2 := by
      constructor <;> intro H
      --Squaring both sides gives the following.
      have H0 : (Real.sqrt (11 * x + 3) - Real.sqrt (2 - x))^2 = (Real.sqrt (9 * x + 7) - Real.sqrt (x - 2))^2 := by
        exact congrFun (congrArg HPow.hPow H) 2
      --Expanding the squares gives the following.
      have H1 : (Real.sqrt (11 * x + 3) - Real.sqrt (2 - x))^2 = (Real.sqrt (11 * x + 3))^2 + (Real.sqrt (2 - x))^2 - 2 * (Real.sqrt (11 * x + 3) * Real.sqrt (2 - x)) := by ring
      --Show (Real.sqrt (11 * x + 3))^2 = 11 * x + 3.
      have H11 : (Real.sqrt (11 * x + 3))^2 = 11 * x + 3 := Real.sq_sqrt h1
      --Show (Real.sqrt (2 - x))^2 = 2 - x.
      have H12 : (Real.sqrt (2 - x))^2 = 2 - x := Real.sq_sqrt h2
      rw [H11, H12] at H1
      --Expanding the squares gives the following.
      have H2 : (Real.sqrt (9 * x + 7) - Real.sqrt (x - 2))^2 = (Real.sqrt (9 * x + 7))^2 + (Real.sqrt (x - 2))^2 - 2 * (Real.sqrt (9 * x + 7) * Real.sqrt (x - 2)) := by ring
      --Show (Real.sqrt (9 * x + 7))^2 = 9 * x + 7.
      have H21 : (Real.sqrt (9 * x + 7))^2 = 9 * x + 7 := Real.sq_sqrt h3
      --SHow (Real.sqrt (x - 2))^2 = x - 2.
      have H22 : (Real.sqrt (x - 2))^2 = x - 2 := Real.sq_sqrt h4
      rw [H21, H22] at H2
      rw [H1, H2] at H0
      --Simplifying.
      rw [← Real.sqrt_mul,← Real.sqrt_mul] at H0
      rw [show (11 * x + 3) * (2 - x) = 6 + 19 * x - 11 * x^2 by ring] at H0
      rw [show (9 * x + 7) * (x - 2) = 9 * x^2 - 11 * x - 14 by ring] at H0
      --Show Real.sqrt (6 + 19 * x - 11 * x^2) = Real.sqrt (9 * x^2 - 11 * x - 14).
      have H3 : Real.sqrt (6 + 19 * x - 11 * x^2) = Real.sqrt (9 * x^2 - 11 * x - 14) := by linarith
      --Show (Real.sqrt (6 + 19 * x - 11 * x^2))^2 = (Real.sqrt (9 * x^2 - 11 * x - 14))^2.
      have H4 : (Real.sqrt (6 + 19 * x - 11 * x^2))^2 = (Real.sqrt (9 * x^2 - 11 * x - 14))^2 := by
        exact congrFun (congrArg HPow.hPow H3) 2
      --Show (Real.sqrt (6 + 19 * x - 11 * x^2))^2 = 6 + 19 * x - 11 * x^2.
      have H5 : (Real.sqrt (6 + 19 * x - 11 * x^2))^2 = 6 + 19 * x - 11 * x^2 := by
        refine Real.sq_sqrt ?_
        have :  6 + 19 * x - 11 * x ^ 2 = (11 * x + 3) * (2 - x) := by ring
        have : (11 * x + 3) * (2 - x) ≥ 0 := by
          apply mul_nonneg
          exact h1
          exact h2
        linarith
      --Show (Real.sqrt (9 * x^2 - 11 * x - 14))^2 = 9 * x^2 - 11 * x - 14.
      have H6 : (Real.sqrt (9 * x^2 - 11 * x - 14))^2 = 9 * x^2 - 11 * x - 14 := by
        refine Real.sq_sqrt ?_
        have : 9 * x^2 - 11 * x - 14 = (9 * x + 7) * (x - 2) := by ring
        have : (9 * x + 7) * (x - 2) ≥ 0 := by
          apply mul_nonneg
          exact h3
          exact h4
        linarith
      rw [H5, H6] at H4
      have H7 : 2 * x^2 - 3 * x - 2 = 0 := by linarith
      have H8 : (2 * x + 1) * (x - 2) = 0 := by linarith
      have H81 : 2 * x + 1 = 0 ∨ x - 2 = 0 := mul_eq_zero.mp H8
      --We show that 2 * x + 1 = 0 is impossible.
      have H9 : ¬ 2 * x + 1 = 0 := by
        intro h
        have : x = (- 1 / 2) := by linarith
        rw [this] at h4
        linarith
      have H10 : x - 2 = 0 := by tauto
      have : x = 2 := by linarith
      exact this
      exact h3
      exact h1

      rw [H]
      norm_num