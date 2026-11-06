import Mathlib

/-- Find the value of $(52 + 6 \sqrt{43})^(3/2) - (52 - 6 \sqrt{43})^(3/2).  -/
theorem algebra_21745 : Real.sqrt (52 + 6 * Real.sqrt 43) ^ 3 - Real.sqrt (52 - 6 * Real.sqrt 43) ^ 3 = 828 := by
  -- Suppose that $52 + 6 \sqrt{43}$ is in the form of $(a + b \sqrt{43})^2$.
  -- We can see that $52 + 6 \sqrt{43} = (\sqrt{43} + 3)^2$.
  have is_sq : 52 + 6 * Real.sqrt 43 = (Real.sqrt 43 + 3)^2 := by
    rw[add_pow_two, Real.sq_sqrt (by simp)]
    ring
  -- Repeating this for $52 - 6 \sqrt{43}$, we can see that the only feasible possibility is $(\sqrt{43} - 3)^2$.
  have is_sq' : 52 - 6 * Real.sqrt 43 = (Real.sqrt 43 - 3)^2 := by
    rw[sub_pow_two, Real.sq_sqrt (by simp)]
    ring
  -- Rewriting, we get $(\sqrt{43} + 3)^23- (\sqrt{43} - 3)^3$.
  rw[is_sq, is_sq']
  rw[Real.sqrt_sq (x := √43 + 3), Real.sqrt_sq (x := √43 - 3)]
  -- Using the difference of cubes,
  · have difference_of_cubes {a b : ℝ} : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by ring
    rw[difference_of_cubes]
    -- we get that this equals
    -- $(\sqrt{43} + 3 - \sqrt{43} + 3) ((43 + 6\sqrt{43} + 9) + (43-9) + (43 - 6\sqrt{43} + 9)) = 6 (3 \cdot 43 + 9) = 828
    have : ((√43 + 3) ^ 2 + (√43 + 3) * (√43 - 3) + (√43 - 3) ^ 2) =
        ((√43+3) + (√43-3))^2 - (√43 + 3) * (√43 - 3) := by
      rw[add_pow_two (a := √43 + 3)]
      ring
    rw[this, add_sub_sub_cancel, add_add_sub_cancel, ← two_mul, ← two_mul, mul_pow, ← sq_sub_sq, Real.sq_sqrt (by simp)]
    ring
  -- to be allowed to square the root, we establish positivity of all the numbers involved.
  · rw[sub_nonneg, ← sq_le_sq₀]
    · rw[Real.sq_sqrt (by simp)]
      linarith
    · linarith
    · apply Real.sqrt_nonneg
  · exact add_nonneg (Real.sqrt_nonneg _) (by simp)