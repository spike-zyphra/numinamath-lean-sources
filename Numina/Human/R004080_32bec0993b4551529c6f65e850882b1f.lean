import Mathlib

/- 5. (5 points) Solve the system of equations:


$$

\left\{\begin{array}{c}
x^{3}+2 y=y^{3}+14 x \\
\frac{y^{2}+1}{x^{2}+1}=3
\end{array}\right.

$$
 -/
theorem algebra_236479 {x y : ℝ} :
    (x^3 + 2 * y = y^3 + 14 * x) ∧ ((y^2 + 1) / (x^2 + 1) = 3)
    ↔((x = 0 ∧ y = Real.sqrt 2)
    ∨ (x = 0 ∧ y = -Real.sqrt 2)
    ∨ (x = Real.sqrt 2 ∧ y = -2 * Real.sqrt 2)
    ∨ (x = -Real.sqrt 2 ∧ y = 2 * Real.sqrt 2))
    := by
      -- if x^2 = y, then x = √y or -√y
      have sq_eq : ∀ {x y : ℝ}, x ^ 2 = y → x = √y ∨ x = -√y := by
        intro x y hh
        refine mul_self_eq_mul_self_iff.mp ?_
        have h : 0 ≤ y := by
          rw [←hh]
          exact sq_nonneg x
        rw [Real.mul_self_sqrt h]
        convert hh
        exact (pow_two x).symm

      -- if x is positive and √x = y, then x = y ^ 2
      have sqrt_eq : ∀ {x y : ℝ}, 0 ≤ x → √x = y → x = y ^ 2 := by
        intro x y xh hh
        have yh : 0 ≤ y := by
          rw [←hh]
          positivity
        exact (Real.sqrt_eq_iff_eq_sq xh yh).mp hh

      -- a negative number to the power of 3 is negative
      have pow_three_neg : ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) := by
        -- because 3 is odd
        refine Odd.neg_pow ?_
        decide

      -- √x ^ 3 = x * √x
      have sqrt_pow_three : ∀ {x : ℝ}, 0 ≤ x → √x ^ 3 = x * √x := by
        intro x xh
        rw [pow_three']
        simp only [xh, Real.mul_self_sqrt]

      -- so √2 ^ 3 = 2 * √2
      have sqrt_pow_three_two : √(2 : ℝ) ^ 3 = 2 * √2 := sqrt_pow_three zero_le_two

      constructor
      -- first find possible solutions
      · intro ⟨h1, h2⟩
        -- consider x = 0
        by_cases h : x = 0
        · subst h
          -- then we have y ^ 2 + 1 = 3
          have y_sq : y ^ 2 = 2 := by linarith only [h2]
          -- so y = ±√2
          have y_eq : y = √2 ∨ y = -√2 := sq_eq y_sq
          tauto
        -- then x ≠ 0
        · have ne_zero : (x ^ 2 + 1) ≠ 0 := by positivity
          replace h2 := (div_eq_iff ne_zero).mp h2
          replace h2 : y ^ 2 = 3 * x ^ 2 + 2 := by linarith

          -- we have a quadratic expression for x, 3 * x ^ 2 + 2 = (x ^ 2 - 14) ^ 2 / (9 * x ^ 2)
          have quadratic : 3 * x ^ 2 + 2 = (x ^ 2 - 14) ^ 2 / (9 * x ^ 2) := by
            -- 3 * x ^ 2 + 2 is positive
            have nonneg : 0 ≤ (3 * x ^ 2 + 2) := by positivity

            -- √(3 * x ^ 2 + 2) ^ 3 = (3 * x ^ 2 + 2) * √(3 * x ^ 2 + 2)
            have pow_three : √(3 * x ^ 2 + 2) ^ 3
              = (3 * x ^ 2 + 2) * √(3 * x ^ 2 + 2) := sqrt_pow_three nonneg

            -- 3x is non-zero
            have ne_zero : (3 * x) ≠ 0 := by
              simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
              exact h

            -- consider cases of y = ±√(3 * x ^ 2 + 2)
            rcases sq_eq h2 with pos | neg
            -- replace y in x ^ 3 + 2 * y = y ^ 3 + 14 * x
            · rw [pos, pow_three] at h1
              -- isolate x ^ 3 on LHS
              replace h1 : x ^ 3 = 3 * x ^ 2 * √(3 * x ^ 2 + 2) + 14 * x := by linarith

              -- divide by x
              apply_fun (· / x) at h1
              convert_to x ^ 2 = 3 * x * √(3 * x ^ 2 + 2) + 14 at h1
              · field_simp
                ring_nf
              · field_simp
                ring_nf

              -- simplify
              replace h1 : √(3 * x ^ 2 + 2) * (3 * x) = x ^ 2 - 14 := by linarith
              -- isolate √(3 * x ^ 2 + 2) on LHS
              replace h1 := eq_div_of_mul_eq ne_zero h1
              -- square both sides
              replace h1 := sqrt_eq nonneg h1
              -- we're done
              convert h1
              ring
            -- replace y in x ^ 3 + 2 * y = y ^ 3 + 14 * x
            · rw [neg, pow_three_neg, pow_three] at h1
              -- isolate x ^ 3 on LHS
              replace h1 : x ^ 3 = -3 * x ^ 2 * √(3 * x ^ 2 + 2) + 14 * x := by linarith
              -- divide by x
              apply_fun (· / x) at h1
              convert_to x ^ 2 = -3 * x * √(3 * x ^ 2 + 2) + 14 at h1
              · field_simp
                ring_nf
              · field_simp
                ring_nf

              -- simplify
              replace h1 : √(3 * x ^ 2 + 2) * (3 * x) = -(x ^ 2 - 14) := by linarith
              -- isolate √(3 * x ^ 2 + 2) on LHS
              replace h1 := eq_div_of_mul_eq ne_zero h1
              -- square both sides
              replace h1 := sqrt_eq nonneg h1
              -- we're done
              convert h1
              ring

          -- write quadratic in normal form (13 * (x ^ 2 * x ^ 2) + 23 * (x ^ 2) + (-98) = 0)
          have ne_zero : 9 * x ^ 2 ≠ 0 := by positivity

          replace quadratic := (eq_div_iff ne_zero).mp quadratic

          replace quadratic : 13 * (x ^ 2 * x ^ 2) + 23 * (x ^ 2) + (-98) = 0 := by
            ring_nf at quadratic ⊢
            linarith

          -- the discriminant is equal to 75 * 75
          have discrim_eq : discrim (13 : ℝ) 23 (-98) = 75 * 75 := by
            unfold discrim
            ring

          -- leading coefficient is not zero
          have a_ne_zero : (13 : ℝ) ≠ 0 := by norm_num

          -- the roots are 2 and -(49 / 13)
          have roots := (quadratic_eq_zero_iff a_ne_zero discrim_eq _).mp quadratic
          norm_num at roots

          -- consider cases of roots
          rcases roots with r1 | r2
          -- let x ^ 2 = 2
          -- then y ^ 2 = 8
          · rw [r1] at h2
            norm_num at h2

            -- √8 = 2 * √2
            have sqrt_eight : √8 = 2 * √2 := by
              convert_to √(2 * 2 * 2) = 2 * √2
              · norm_num
              rw [Real.sqrt_mul]
              simp only [Nat.ofNat_nonneg, Real.sqrt_mul_self]
              positivity

            -- consider possible values of x and y
            rcases sq_eq r1 with h3 | h4
            · rcases sq_eq h2 with h5 | h6
              -- (x, y) = (√2, √8)
              · rw [sqrt_eight] at h5
                -- but then we have (2 + 2 * 2) * √2 = (2 ^ 3 * 2 + 14) * √2
                rw [h3, h5, mul_pow, sqrt_pow_three_two] at h1
                rw [←mul_assoc, ←mul_assoc, ←add_mul, ←add_mul] at h1
                -- contradiction
                norm_num at h1
              -- (x, y) = (√2, -√8)
              · rw [sqrt_eight, ←neg_mul] at h6
                rw [h3, h6]
                simp only [and_self, true_or, or_true]
            · rcases sq_eq h2 with h5 | h6
              -- (x, y) = (-√2, √8)
              · rw [sqrt_eight] at h5
                rw [h4, h5]
                simp only [and_self, true_or, or_true]
              -- (x, y) = (-√2, -√8)
              · rw [sqrt_eight, ←neg_mul] at h6
                -- but then we have -(√2 * 6) = -(√2 * 30)
                rw [h4, h6, mul_pow, sqrt_pow_three_two,
                  pow_three_neg, pow_three_neg, sqrt_pow_three_two] at h1
                ring_nf at h1
                -- contradiction
                norm_num at h1
          -- other root is x ^ 2 = -(49 / 13)
          -- but x ^ 2 is positive
          · have pos : (0 : ℝ) < x ^ 2 := by positivity
            -- and -(49 / 13) is negative
            have neg : -(49 / 13) < (0 : ℝ) := by linarith

            -- contradiction
            linarith

      -- prove that every solution is valid
      · rintro (⟨xh, yh⟩ | ⟨xh, yh⟩ | ⟨xh, yh⟩ | ⟨xh, yh⟩)
        -- (0, √2) is valid
        · rw [xh, yh, sqrt_pow_three_two]
          norm_num
        -- (0, -√2) is valid
        · rw [xh, yh, pow_three_neg, sqrt_pow_three_two]
          norm_num
        -- (-√2, -2 * √2) is valid
        · simp only [xh, yh, sqrt_pow_three_two, mul_pow]
          norm_num
          ring_nf
        -- (-√2, 2 * √2) is valid
        · simp only [xh, yh, sqrt_pow_three_two, mul_pow, pow_three_neg]
          norm_num
          ring_nf