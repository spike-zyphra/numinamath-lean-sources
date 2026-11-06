import Mathlib

/-What is the least possible value of the sum $|x - 1| + |x - 1.5| + |x - 2|$?-/
theorem algebra_19524 :
    IsLeast {y : ℝ | ∃ x, y = abs (x - 1) + abs (x - 1.5) + abs (x - 2)} 1 := by
  constructor
  · -- Prove that 1 is in the set.
    simp
    use 1.5
    norm_num
    rw [show abs (1 / (2 : ℝ)) = 1 / 2 by simp]
    linarith
  · -- We tackle this with some careful casework
    apply mem_lowerBounds.mpr
    simp
    intro x
    by_cases h₁: 2 ≤ x
    · -- Case 1: $x\ge 2$.  We then have $|x-1| + |x-1.5| + |x-2| = (x-1) + (x-1.5) + (x-2) = 3x - 4.5$.  Since the smallest value of $x$ in this case is $2$, the smallest possible value of the sum in this case is $3(2) - 4.5 = 1.5$.
      rw [abs_eq_self.mpr (show 0 ≤ x - 2 by linarith)]
      rw [abs_eq_self.mpr (show 0 ≤ x - 1.5 by norm_num; linarith)]
      rw [abs_eq_self.mpr (show 0 ≤ x - 1 by linarith)]
      norm_num
      linarith

    by_cases h₂: 1.5 ≤ x
    · -- Case 2: $1.5\le x < 2$.  We then have  \begin{align*}
      -- |x-1| + |x-1.5| + |x-2| & = (x-1) + (x-1.5) + (-(x-2)) \\
      -- & = 2x - 2.5 -x+2 \\
      -- & = x -0.5.
      -- \end{align*} Since the smallest possible value of $x$ in this case is $1.5$, the smallest possible value of the sum in this case is $1.5-0.5 = 1$.
      norm_num at h₂
      rw [abs_eq_neg_self.mpr (show x - 2 ≤ 0 by linarith)]
      rw [abs_eq_self.mpr (show 0 ≤ x - 1.5 by norm_num; linarith)]
      rw [abs_eq_self.mpr (show 0 ≤ x - 1 by linarith)]
      norm_num
      linarith

    by_cases h₃: 1 ≤ x
    · -- Case 3: $1 \le x < 1.5$.  We then have  \begin{align*}
      -- |x-1| + |x-1.5| + |x-2| & = (x-1) - (x-1.5) - (x-2) \\
      -- & = x-1 -x + 1.5-x+2 \\
      -- & = -x +2.5.
      -- \end{align*} Since $x$ is less than 1.5, the sum in this case is greater than $-1.5+2.5 = 1$.
      rw [abs_eq_neg_self.mpr (show x - 2 ≤ 0 by linarith)]
      rw [abs_eq_neg_self.mpr (show x - 1.5 ≤ 0 by linarith)]
      rw [abs_eq_self.mpr (show 0 ≤ x - 1 by linarith)]
      linarith

    -- Case 4: $x < 1$.  We then have  \begin{align*}
    -- |x-1| + |x-1.5| + |x-2| & = -(x-1) - (x-1.5) - (x-2) \\
    -- & = -3x + 4.5.
    -- \end{align*} Since $x$ is less than 1, the sum in this case is greater than $-3(1) + 4.5 = 1.5$.
    rw [abs_eq_neg_self.mpr (show x - 2 ≤ 0 by linarith)]
    rw [abs_eq_neg_self.mpr (show x - 1.5 ≤ 0 by linarith)]
    rw [abs_eq_neg_self.mpr (show x - 1 ≤ 0 by linarith)]
    linarith
    -- Reviewing these cases, we see that the least possible sum is $\boxed{1}$.  As an extra challenge, see if you can find a quick solution to this problem by thinking about the graph of $y = | x-1| + |x-1.5| + |x-2|$.
