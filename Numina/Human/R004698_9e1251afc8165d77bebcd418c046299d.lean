import Mathlib

/-
6. The integer solutions $(x, y)$ of the equation $\frac{1}{y}+\frac{1}{2(x+y)}=\frac{1}{y^{2}}$ are ( ).
(A) 0 sets
(B) 1 set
(C) finite sets (more than 1 set)
(D) infinitely many sets
-/
theorem algebra_304904 : {((x, y) : ℤ × ℤ) | (y ≠ 0) ∧ x + y ≠ 0 ∧ 1 / y + (1 : ℝ) / (2 * (x + y)) = 1 / y ^ 2 }= {(-4, 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_singleton_iff]
  apply Iff.intro
  · simp only [ne_eq, Set.mem_setOf_eq]
    rintro ⟨hy, hxy, h_eq⟩
    -- Promote hy and hxy to ℝ to use them in field_simp and manipulation
    have hy_real : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hxy_real : (x + y : ℝ) ≠ 0 := by exact_mod_cast hxy
    have hden1 : 2 * ((x : ℝ) + (y : ℝ)) ≠ 0 := by -- Prove denominator `2*(x+y)` is non-zero
      apply mul_ne_zero
      · norm_num -- 2 ≠ 0
      · exact hxy_real
    have hden2 : (y : ℝ) ^ 2 ≠ 0 := by -- Prove denominator `y^2` is non-zero
      apply pow_ne_zero
      · exact hy_real
    -- Manipulate the equation to clear denominators
    -- Start with: 1 / y + 1 / (2 * (x + y)) = 1 / y ^ 2
    -- Rewrite as: (1/y) - (1/y^2) = -1 / (2 * (x+y))
    have h_eq_manip : (1 : ℝ) / y - 1 / y ^ 2 = -1 / (2 * (x + y)) := by
      rw [← eq_sub_iff_add_eq] at h_eq
      rw [h_eq]
      ring
    -- Combine terms on the left side
    -- (y - 1) / y^2 = -1 / (2 * (x + y))
    have h_eq_combined : (y - 1 : ℝ) / y ^ 2 = -1 / (2 * (x + y)) := by
      rw [← h_eq_manip]
      field_simp [hy_real] -- Apply field_simp again to simplify further if needed
      ring
    -- Cross-multiply: (y - 1) * 2 * (x + y) = -1 * y^2
    have h_cross_mul : (y - 1 : ℝ) * (2 * (x + y)) = -1 * y ^ 2 := by
      rwa [div_eq_div_iff hden2 hden1] at h_eq_combined
    -- Expand and rearrange the equation to get a polynomial in integers
    -- 2(y - 1)(x + y) = -y^2
    -- 2(xy + y^2 - x - y) = -y^2
    -- 2xy + 2y^2 - 2x - 2y = -y^2
    -- 2xy + 3y^2 - 2x - 2y = 0
    have h_poly_real : 2 * (x : ℝ) * y + 3 * y ^ 2 - 2 * x - 2 * y = 0 := by
      calc
        2 * (x : ℝ) * y + 3 * y ^ 2 - 2 * x - 2 * y
        _ = 2 * x * y + 2 * y ^ 2 - 2 * x - 2 * y + y ^ 2 := by ring
        _ = 2 * (x * y + y ^ 2 - x - y) + y ^ 2 := by ring
        _ = 2 * ((y - 1) * (x + y)) + y ^ 2 := by norm_cast; ring
        _ = (y - 1) * (2 * (x + y)) + y ^ 2 := by ring
        _ = -1 * y ^ 2 + y ^ 2 := by rw [h_cross_mul]
        _ = 0 := by ring
    -- Cast the equation back to integers
    have h_poly_int : 2 * x * y + 3 * y ^ 2 - 2 * x - 2 * y = 0 := by
      exact_mod_cast h_poly_real
    -- Factor the integer polynomial
    -- y(2x + 3y) - 2(x + y) = 0
    -- y(3y - 2) = 2x(1 - y)
    have h_factored : y * (3 * y - 2) = 2 * x * (1 - y) := by
      linarith [h_poly_int]

    -- Consider the case y = 1
    have hy_ne_1 : y ≠ 1 := by
      intro hy_eq_1
      subst y
      simp only [one_mul, sub_self, mul_zero, mul_one, sub_neg_eq_add] at h_factored
      norm_num at h_factored -- This simplifies 3 * 1 - 2 to 1, so 1 = 0
    -- Since y ≠ 1, 1 - y ≠ 0
    have hone_minus_y_ne_zero : 1 - y ≠ 0 := by
      intro h_eq_zero
      apply hy_ne_1
      linarith
    -- From y(3y - 2) = 2x(1 - y), we see that (1 - y) must divide y(3y - 2)
    -- Let's check the divisibility more carefully.
    -- y(3y - 2) = y(3(y-1) + 3 - 2) = y(3(y-1) + 1) = 3y(y-1) + y
    --           = 3(y-1+1)(y-1) + (y-1+1) = (3(y-1)+3)(y-1) + (y-1) + 1
    --           = 3(y-1)^2 + 3(y-1) + (y-1) + 1 = 3(y-1)^2 + 4(y-1) + 1
    -- Since 1 - y divides y(3y-2), and 1 - y obviously divides 3(y-1)^2 + 4(y-1),
    -- it must be that 1 - y divides 1.
    have h_div : (1 - y) ∣ y * (3 * y - 2) := by
      use (2 * x)
      rw [h_factored]
      ring
    have h_div_1 : (1 - y) ∣ 1 := by
      have h_rewrite : y * (3 * y - 2) = (-3 * y - 1) * (1 - y) + 1 := by
        ring
      rw [h_rewrite] at h_div
      have := dvd_sub h_div (dvd_mul_left (1 - y) (-3 * y - 1))
      simp at this
      exact this
    -- The only divisors of 1 are 1 and -1.
    -- So 1 - y = 1 or 1 - y = -1
    apply isUnit_of_dvd_one at h_div_1
    apply Int.isUnit_eq_one_or at h_div_1
    rcases h_div_1 with hp | hn
    · -- Case 1: 1 - y = 1  => y = 0. This contradicts hy ≠ 0.
      have hy_eq_0 : y = 0 := by linarith [hp]
      contradiction
    · -- Case 2: 1 - y = -1 => y = 2.
      have hy_eq_2 : y = 2 := by linarith [hn]
      subst y
      -- Substitute y = 2 back into the factored equation h_factored
      -- 2 * (3 * 2 - 2) = 2 * x * (1 - 2)
      -- 2 * (6 - 2) = 2 * x * (-1)
      -- 2 * 4 = -2x
      -- 8 = -2x
      -- x = -4
      simp only [mul_one, mul_add, mul_sub, mul_neg, sub_neg_eq_add, *] at h_factored
      norm_num at h_factored -- Simplifies to 8 = -2 * x
      have hx_eq_neg4 : x = -4 := by linarith [h_factored]
      -- We have shown y=2 and x=-4, which is the goal
      exact congrFun (congrArg Prod.mk hx_eq_neg4) 2
  · rintro ⟨rfl, rfl⟩
    norm_num