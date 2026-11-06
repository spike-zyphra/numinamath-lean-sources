import Mathlib

open Real

/- 7. $[4]$ For any real number $\alpha$, define
$$
\operatorname{sign}(\alpha)=\left\{\begin{array}{ll}
+1 & \text { if } \alpha>0 \\
0 & \text { if } \alpha=0 \\
-1 & \text { if } \alpha<0
\end{array}\right.
$$

How many triples $(x, y, z) \in \mathbb{R}^{3}$ satisfy the following system of equations
$$
\begin{array}{l}
x=2018-2019 \cdot \operatorname{sign}(y+z) \\
y=2018-2019 \cdot \operatorname{sign}(z+x) \\
z=2018-2019 \cdot \operatorname{sign}(x+y) ?
\end{array}
$$ -/
theorem algebra_172377 :
    {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * (if y + z > 0 then 1 else (if y + z = 0 then 0 else -1)) ∧
      y = 2018 - 2019 * (if z + x > 0 then 1 else (if z + x = 0 then 0 else -1)) ∧
      z = 2018 - 2019 * (if x + y > 0 then 1 else (if x + y = 0 then 0 else -1))}.ncard = 3 := by

  -- First, we prove that the solution set equals exactly three specific points
  have h1 : {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * (if y + z > 0 then 1 else (if y + z = 0 then 0 else -1)) ∧
      y = 2018 - 2019 * (if z + x > 0 then 1 else (if z + x = 0 then 0 else -1)) ∧
      z = 2018 - 2019 * (if x + y > 0 then 1 else (if x + y = 0 then 0 else -1))} = {(-1, -1, 4037), (-1, 4037, -1), (4037, -1, -1)} := by

    -- We use extensionality to show the sets are equal
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- Assume the equations hold, prove (x, y, z) is one of the three solutions
      rintro ⟨hx, hy, hz⟩

      -- First, we show that x must be one of three possible values: -1, 2018, or 4037
      have h1 : x = -1 ∨ x = 2018 ∨ x = 4037 := by
        by_cases h1 : y + z > 0
        · -- If y + z > 0, then sign(y + z) = 1, so x = 2018 - 2019 * 1 = -1
          rw [if_pos h1] at hx
          norm_num at hx
          left
          linarith
        · -- If y + z ≤ 0, then either y + z = 0 or y + z < 0
          by_cases h2 : y + z = 0
          · -- If y + z = 0, then sign(y + z) = 0, so x = 2018 - 2019 * 0 = 2018
            rw [if_neg h1, if_pos h2] at hx
            norm_num at hx
            right
            left
            linarith
          · -- If y + z < 0, then sign(y + z) = -1, so x = 2018 - 2019 * (-1) = 4037
            rw [if_neg h1, if_neg h2] at hx
            norm_num at hx
            right
            right
            linarith

      -- Similarly, we show that y must be one of three possible values: -1, 2018, or 4037
      have h2 : y = -1 ∨ y = 2018 ∨ y = 4037 := by
        by_cases h1 : z + x > 0
        · -- If z + x > 0, then sign(z + x) = 1, so y = 2018 - 2019 * 1 = -1
          rw [if_pos h1] at hy
          norm_num at hy
          left
          linarith
        · -- If z + x ≤ 0, then either z + x = 0 or z + x < 0
          by_cases h2 : z + x = 0
          · -- If z + x = 0, then sign(z + x) = 0, so y = 2018 - 2019 * 0 = 2018
            rw [if_neg h1, if_pos h2] at hy
            norm_num at hy
            right
            left
            linarith
          · -- If z + x < 0, then sign(z + x) = -1, so y = 2018 - 2019 * (-1) = 4037
            rw [if_neg h1, if_neg h2] at hy
            norm_num at hy
            right
            right
            linarith

      -- And finally, we show that z must be one of three possible values: -1, 2018, or 4037
      have h3 : z = -1 ∨ z = 2018 ∨ z = 4037 := by
        by_cases h1 : x + y > 0
        · -- If x + y > 0, then sign(x + y) = 1, so z = 2018 - 2019 * 1 = -1
          rw [if_pos h1] at hz
          norm_num at hz
          left
          linarith
        · -- If x + y ≤ 0, then either x + y = 0 or x + y < 0
          by_cases h2 : x + y = 0
          · -- If x + y = 0, then sign(x + y) = 0, so z = 2018 - 2019 * 0 = 2018
            rw [if_neg h1, if_pos h2] at hz
            norm_num at hz
            right
            left
            linarith
          · -- If x + y < 0, then sign(x + y) = -1, so z = 2018 - 2019 * (-1) = 4037
            rw [if_neg h1, if_neg h2] at hz
            norm_num at hz
            right
            right
            linarith

      -- Now we check all 27 possible combinations of x, y, z values
      -- and eliminate those that don't satisfy the original equations
      rcases h1 with hx | hx | hx <;> rcases h2 with hy | hy | hy <;> rcases h3 with hz | hz | hz <;>
      try {
        simp [hx, hy, hz] at *
        all_goals
          try {
            linarith
          }
          try {
            norm_num at *
          }
      }
    · -- Assume (x, y, z) is one of the three solutions, prove the equations hold
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- Case (-1, -1, 4037)
        norm_num
      · -- Case (-1, 4037, -1)
        norm_num
      · -- Case (4037, -1, -1)
        norm_num

  -- Finally, we use our result to conclude that there are exactly 3 solutions
  rw [h1]
  norm_num
