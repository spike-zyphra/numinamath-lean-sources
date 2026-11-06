import Mathlib

/- Let's prove that if we eliminate the parameter $ t $ from the system of equations


$$

\begin{gathered}
x=1+2 t-2 t^{2} \ldots \\
y=2(1+t) \sqrt{1-t^{2}} \ldots
\end{gathered}

$$


we arrive at the equation


$$

y^{4}+2 y^{2}\left(x^{2}-12 x+9\right)+x^{4}+8 x^{3}+18 x^{2}-27=0 \ldots

$$
 -/
theorem algebra_237667 {x y : ℝ} (t : ℝ) (h1 : x = 1 + 2 * t - 2 * t ^ 2)
  (h2 : y = 2 * (1 + t) * Real.sqrt (1 - t ^ 2))
  (pos : 0 ≤ (1 - t ^ 2))
  : y ^ 4 + 2 * y ^ 2 * (x ^ 2 - 12 * x + 9) + x ^ 4 + 8 * x ^ 3 + 18 * x ^ 2 - 27 = 0
  := by
    -- express x and t equation as a quadratic where t is the variable
    have quad_eq : 2 * (t * t) + (-2) * t + (x - 1) = 0 := by linarith

    -- the discriminant is equal to 4 * (3 - 2 * x)
    have discrim_eq : discrim 2 (-2) (x - 1) = 4 * (3 - 2 * x) := by
      norm_num [discrim]
      ring_nf

    -- we have √(3 - x * 2) ^ 2 = 3 - x * 2
    have as_sqrt : √(3 - x * 2) ^ 2 = 3 - x * 2 := by
      -- because 3 - x * 2 is non-negative
      refine Real.sq_sqrt ?_

      -- express as function of t
      simp only [h1]

      -- offset the function by setting t = t' + (1 / 2)
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + (1 / 2) := by
        exists t - (1 / 2)
        norm_num

      -- simplify to t' ^ 2 * 4
      ring_nf

      -- clearly t' ^ 2 * 4 is non-negative
      positivity

    -- we can express the discriminant as a square
    have square_discrim : 4 * (3 - x * 2) = ((2 : ℝ) * √(3 - x * 2)) * (2 * √(3 - x * 2)) := by
      ring_nf
      rw [as_sqrt]
      ring

    rw [mul_comm 2 x, square_discrim] at discrim_eq

    -- two is not zero
    have two_ne_zero : (2 : ℝ) ≠ 0 := by linarith

    -- then we have that t = (1 ± √(3 - x * 2)) / 2
    have roots : t = (1 + √(3 - x * 2)) / 2 ∨ t = (1 - √(3 - x * 2)) / 2 := by
      have roots := (quadratic_eq_zero_iff two_ne_zero discrim_eq t).mp quad_eq

      norm_num [←mul_one_add, ←mul_one_sub] at roots

      have four_eq_two_mul_two : (4 : ℝ) = 2 * 2 := by linarith

      rw [four_eq_two_mul_two, mul_div_mul_left _ _ two_ne_zero,
        mul_div_mul_left _ _ two_ne_zero] at roots
      exact roots

    -- given equation for y gives us y ^ 2 = 4 * (1 + t) ^ 2 * (1 - t ^ 2)
    have y_sq_eq : y ^ 2 = 4 * (1 + t) ^ 2 * (1 - t ^ 2) := by
      apply_fun (· ^ 2) at h2
      convert h2
      norm_num [mul_pow, mul_pow]
      exact Or.inl (Real.sq_sqrt pos).symm

    -- so y ^ 2 = (x ∓ √(3 - 2 * x)) * (6 - x ± 3 * √(3 - 2 * x))
    have y_sq_cases : y ^ 2 = (x - √(3 - 2 * x)) * (6 - x + 3 * √(3 - 2 * x))
      ∨ y ^ 2 = (x + √(3 - 2 * x)) * (6 - x - 3 * √(3 - 2 * x)) := by
        -- sign depends on sign of t
        -- we'll have
        -- 1. t ^ 2 = (2 - x ± √(3 - 2 * x)) / 2
        -- 2. 1 - t ^ 2 = (x ∓ √(3 - 2 * x)) / 2
        -- 3. (1 + t) ^ 2 = (6 - x ± 3 * √(3 - 2 * x)) / 2
        -- which will give us our wanted expressions for y ^ 2

        rcases roots with eq_pos | eq_neg
          -- in the positive-sign-case...
        · have t_sq : t ^ 2 = (2 - x + √(3 - 2 * x)) / 2 := by
            apply_fun (· ^ 2) at eq_pos
            convert eq_pos
            rw [div_pow]
            norm_num [div_pow, pow_two, mul_add, add_mul]
            rw [←pow_two, as_sqrt]
            ring_nf

          have one_sub_t_sq : 1 - t ^ 2 = (x - √(3 - 2 * x)) / 2 := by
            rw [t_sq]
            ring

          have one_add_t_sq : (1 + t) ^ 2 = (6 - x + 3 * √(3 - 2 * x)) / 2 := by
            rw [eq_pos]
            norm_num [pow_two]
            ring_nf
            rw [as_sqrt]
            ring

          rw [y_sq_eq, one_sub_t_sq, one_add_t_sq]
          refine Or.inl ?_
          ring
          -- in the negative-sign-case...
        · have t_sq : t ^ 2 = (2 - x - √(3 - 2 * x)) / 2 := by
            apply_fun (· ^ 2) at eq_neg
            convert eq_neg
            rw [div_pow]
            norm_num [div_pow, pow_two, mul_sub, sub_mul]
            rw [←pow_two, as_sqrt]
            ring_nf

          have one_sub_t_sq : 1 - t ^ 2 = (x + √(3 - 2 * x)) / 2 := by
            rw [t_sq]
            ring

          have one_add_t_sq : (1 + t) ^ 2 = (6 - x - 3 * √(3 - 2 * x)) / 2 := by
            rw [eq_neg]
            norm_num [pow_two]
            ring_nf
            rw [as_sqrt]
            ring

          rw [y_sq_eq, one_sub_t_sq, one_add_t_sq]
          refine Or.inr ?_
          ring

    -- find expression for x and y without sign cases
    have y_sq_single : (y ^ 2 + (x ^ 2 - 12 * x + 9)) ^ 2 = 4 * (3 - 2 * x) ^ 3 := by
      rcases y_sq_cases with eq_pos | eq_neg
      · have y_sq_eq' : y ^ 2 = -(x ^ 2 - 12 * x + 9) - 2 * (3 - 2 * x) * √(3 - 2 * x) := by
          convert eq_pos using 1
          ring_nf
          rw [as_sqrt]
          ring_nf

        -- move sign case to RHS (now negative)
        replace y_sq_eq' : y ^ 2 + (x ^ 2 - 12 * x + 9) = -2 * (3 - 2 * x) * √(3 - 2 * x) := by linarith
        apply_fun (· ^ 2) at y_sq_eq'
        convert y_sq_eq'
        ring_nf
        rw [as_sqrt]
        ring
      · have y_sq_eq' : y ^ 2 = -(x ^ 2 - 12 * x + 9) + 2 * (3 - 2 * x) * √(3 - 2 * x) := by
          convert eq_neg using 1
          ring_nf
          rw [as_sqrt]
          ring_nf

        -- move sign case to RHS (now positive)
        replace y_sq_eq' : y ^ 2 + (x ^ 2 - 12 * x + 9) = 2 * (3 - 2 * x) * √(3 - 2 * x) := by linarith
        apply_fun (· ^ 2) at y_sq_eq'
        convert y_sq_eq'
        ring_nf
        rw [as_sqrt]
        ring

    -- expand expression with x and y
    ring_nf at y_sq_single

    -- then it's equal to our wanted expression
    linarith only [y_sq_single]