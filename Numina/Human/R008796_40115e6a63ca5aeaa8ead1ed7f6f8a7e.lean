import Mathlib

open Real

/- 10. The sequence $a_{0}, a_{1}, a_{2}, \cdots, a_{n}$ satisfies $a_{0}=\sqrt{3}, a_{n+1}=\left[a_{n}\right]+\frac{1}{\left\{a_{n}\right\}}\left(\left[a_{n}\right],\left\{a_{n}\right\}\right.$ represent the integer part and fractional part of $a_{n}$, respectively), then $a_{2016}=$ $\qquad$ . -/
theorem number_theory_252809 (a : ℕ → ℝ) (ha0 : a 0 = sqrt 3) (han : ∀ n, a (n + 1) = ⌊a n⌋ + 1 / (a n - ⌊a n⌋)) : a 2016 = 3024 + sqrt 3 := by
  -- Derive a formula for a k
  have formula (k : ℕ) : a (2*k + 1) = 3*k + 2 + (√3 - 1) / 2 ∧ a (2*k) = 3*k + √3 := by
    -- Show that floor √3 is 1
    have floor_sqrt_three : ⌊√3⌋ = 1 := by
      rw [Int.floor_eq_iff]
      norm_num
      calc
        √3 = |√3| := symm (abs_eq_self.mpr (show 0 ≤ √3 by positivity))
        _ < 2 := abs_lt_of_sq_lt_sq (show (√3)^2 < 2^2 by norm_num) (show 0 ≤ 2 by positivity)
    -- Use induction on k
    induction k with
    -- Case when k = 0
    | zero =>
      constructor
      · simp
        have : a 1 = 2 + (√3 - 1) / 2 := by
          rw [han 0, ha0, floor_sqrt_three]
          field_simp
          rw [← mul_div_mul_right 1 (√3 - 1) (show √3 + 1 ≠ 0 by positivity)]
          -- Difference of squares to clear denominator
          have : (√3 - 1) * (√3 + 1) = 2 := by rw [mul_comm, ← sq_sub_sq]; simp; norm_num
          rw [this]
          linarith
        tauto
      simp
      tauto
    -- Inductive step
    | succ k hi =>
      -- We make the even case a hypothesis because it is used in the odd case
      have even_case : a (2 * (k + 1)) = 3 * ↑(k + 1) + √3 := by
        simp [mul_add]
        rw [han (2*k + 1)]
        -- Evaluate the floor of a (2*k + 1)
        have a_floor : ⌊a (2*k + 1)⌋ = 3*k + 2 := by
          rw [hi.left, Int.floor_eq_iff]
          simp
          constructor
          -- Prove 0 ≤ (√3 - 1) / 2
          · have : √3 ≥ 1 := by norm_num
            linarith
          -- Prove (√3 - 1) / 2 < 1
          have : √3 - 1 < 2 := by linarith [show √3 < 3 by exact (sqrt_lt (show 0 ≤ 3 by linarith) (show 0 ≤ 3 by linarith)).mpr (by norm_num)]
          linarith
        rw [a_floor, hi.left]
        simp
        -- Rationalize denominator
        rw [← mul_div_mul_right 2 (√3 - 1) (show √3 + 1 ≠ 0 by positivity)]
        have : (√3 - 1) * (√3 + 1) = 2 := by rw [mul_comm, ← sq_sub_sq]; simp; norm_num
        rw [this]
        linarith
      constructor
      -- Odd case
      · rw [han (2*(k + 1))]
        -- Evaluate floor of a 2*(k + 1)
        have a_floor : ⌊a (2*(k + 1))⌋ = 3*k + 4 := by
          rw [even_case, Int.floor_eq_iff]
          simp
          constructor
          -- Prove 3*k + 4 ≤ 3*(k + 1) + √3
          · simp [mul_add, add_assoc]
            rw [show (4 : ℝ) = 3 + 1 by norm_num]
            apply add_le_add_left _
            simp
          -- Prove 3*(k + 1) + √3 < 3*k + 4 + 1
          simp [mul_add, add_assoc]
          rw [show (4 : ℝ) = 3 + 1 by norm_num, add_assoc]
          apply add_lt_add_left _
          norm_num
          -- Show √3 < 2
          calc
            √3 = |√3| := symm (abs_eq_self.mpr (show 0 ≤ √3 by positivity))
            _ < 2 := abs_lt_of_sq_lt_sq (show (√3)^2 < 2^2 by norm_num) (show 0 ≤ 2 by positivity)
        rw [a_floor, even_case]
        -- Simplify the resulting expression
        field_simp
        simp [mul_add, add_assoc, add_mul]
        norm_num
        rw [add_comm 3 _, add_sub_assoc]
        norm_num
        rw [← one_div, add_sub, ← sub_eq_add_neg]
        -- Rationalize denominator
        rw [← mul_div_mul_right 1 (√3 - 1) (show √3 + 1 ≠ 0 by positivity)]
        have : (√3 - 1) * (√3 + 1) = 2 := by rw [mul_comm, ← sq_sub_sq]; simp; norm_num
        rw [this]
        linarith
      -- Even case
      tauto
  -- Use our formula to derive an expression for a 2016
  rw [(formula 1008).right]
  -- Conclude equality
  norm_num