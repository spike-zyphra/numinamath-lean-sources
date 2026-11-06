import Mathlib

open Real Set
open scoped Real

/- [Example 4.4.9] Prove: $\cos \frac{\pi}{7}-\cos \frac{2 \pi}{7}+\cos \frac{3 \pi}{7}=\frac{1}{2}$. -/
theorem algebra_115086 : cos (π/7) - cos (2*π/7) + cos (3*π/7) = 1/2 := by
  -- Abbreviate using variable names
  let c1 := cos (π/7)
  let c2 := cos (2*π/7)
  let c3 := cos (3*π/7)
  let c4 := cos (4*π/7)
  let c5 := cos (5*π/7)
  let c6 := cos (6*π/7)
  let s1 := sin (π/7)
  let s2 := sin (2*π/7)
  let s3 := sin (3*π/7)
  let A := c1 - c2 + c3
  let B := s1 - s2 + s3
  -- Evaluate A^2 and B^2
  have a_sq : A^2 = c1^2 + c2^2 + c3^2 - 2*c1*c2 - 2*c2*c3 + 2*c3*c1 := by ring
  have b_sq : B^2 = s1^2 + s2^2 + s3^2 - 2*s1*s2 - 2*s2*s3 + 2*s3*s1 := by ring
  -- Use the Pythagorean identity
  have c1_sq_add_s1_sq : c1^2 + s1^2 = 1 := by unfold c1 s1; simp
  have c2_sq_add_s2_sq : c2^2 + s2^2 = 1 := by unfold c2 s2; simp
  have c3_sq_add_s3_sq : c3^2 + s3^2 = 1 := by unfold c3 s3; simp
  -- Use cosine addition and subtraction formula to rewrite products
  have c1c3_add_s1s3 : c1*c3 + s1*s3 = c2 := by
    unfold c1 c3 s1 s3 c2
    rw [← cos_sub, show π/7 - 3*π/7 = -(2*π/7) by linarith, cos_neg]
  have c1c3_sub_s1s3 : c1*c3 - s1*s3 = c4 := by
    unfold c1 c3 s1 s3 c4
    rw [← cos_add, show π/7 + 3*π/7 = (4*π/7) by linarith]
  have c1c2_add_s1s2 : c1*c2 + s1*s2 = c1 := by
    unfold c1 c2 s1 s2
    rw [← cos_sub, show π/7 - 2*π/7 = -(π/7) by linarith, cos_neg]
  have c1c2_sub_s1s2 : c1*c2 - s1*s2 = c3 := by
    unfold c1 c2 s1 s2 c3
    rw [← cos_add, show π/7 + 2*π/7 = (3*π/7) by linarith]
  have c2c3_add_s2s3 : c2*c3 + s2*s3 = c1 := by
    unfold c1 c2 c3 s2 s3
    rw [← cos_sub, show 2*π/7 - 3*π/7 = -(π/7) by linarith, cos_neg]
  have c2c3_sub_s2s3 : c2*c3 - s2*s3 = c5 := by
    unfold c2 c3 s2 s3 c5
    rw [← cos_add, show 2*π/7 + 3*π/7 = (5*π/7) by linarith]
  -- Use cosine double angle formula
  have c1_sq_sub_s1_sq : c1^2 - s1^2 = c2 := by
    unfold c1 c2 s1
    rw [← cos_two_mul', show 2*(π/7) = 2*π/7 by linarith]
  have c2_sq_sub_s2_sq : c2^2 - s2^2 = c4 := by
    unfold c2 c4 s2
    rw [← cos_two_mul', show 2*(2*π/7) = 4*π/7 by linarith]
  have c3_sq_sub_s3_sq : c3^2 - s3^2 = c6 := by
    unfold c3 c6 s3
    rw [← cos_two_mul', show 2*(3*π/7) = 6*π/7 by linarith]
  -- Use cosine of supplement
  have c5_eq_neg_c2 : c5 = - c2 := by
    unfold c5 c2
    rw [show 5*π/7 = π - (2*π/7) by linarith, cos_pi_sub]
  have c4_eq_neg_c3 : c4 = - c3 := by
    unfold c4 c3
    rw [show 4*π/7 = π - (3*π/7) by linarith, cos_pi_sub]
  have c6_eq_neg_c1 : c6 = - c1 := by
    unfold c6 c1
    rw [show 6*π/7 = π - (π/7) by linarith, cos_pi_sub]
  -- Use A^2 and B^2 to set up equations
  have a_sq_add_b_sq : A^2 + B^2 = 3 - 4*c1 + 2*c2 := by
    rw [a_sq, b_sq]
    -- linarith will be able to use all of our hypotheses and solve
    linarith
  have a_sq_sub_b_sq : A^2 - B^2 = -c1 + 3*c2 - 5*c3 := by
    rw [a_sq, b_sq]
    linarith
  -- Add the previous two results to get a quadratic
  have two_mul_a_sq : 2*A^2 = 3 - 5*A := by
    calc
      2*A^2 = A^2 + B^2 + (A^2 - B^2) := by ring
      _ = 3 - 5 * (c1 - c2 + c3) := by linarith
      _ = 3 - 5*A := by simp
  -- Factor the quadratic
  have factor_quadratic : (2*A - 1) * (A + 3) = 0 := by nlinarith
  have a_add_three_ne_zero : A + 3 ≠ 0 := by
    have : A + 3 > 0 := by
      -- Show that c2 < 1
      have : c2 ≠ 1 ∧ c2 ≤ 1 := by
        constructor
        · intro hc2
          apply (cos_eq_one_iff_of_lt_of_lt (show -(2*π) < 2*π/7 by linarith [pi_pos]) (show 2*π/7 < 2*π by linarith [pi_pos])).mp at hc2
          norm_num at hc2
          exact pi_ne_zero hc2
        linarith [cos_le_one (2*π/7)]
      have : c2 < 1 := lt_of_le_of_ne (this.2) (this.1)
      unfold A c1 c2 c3
      calc
        c1 - c2 + c3 + 3 = 1 + c1 + 1 - c2 + 1 + c3 := by ring
        _ ≥ 1 - c2 := by linarith [neg_one_le_cos (π/7), neg_one_le_cos (3*π/7)]
        _ > 0 := by linarith [this]
    linarith
  apply (mul_eq_zero_iff_right a_add_three_ne_zero).mp at factor_quadratic
  -- Now that we know 2*A - 1 = 0, we can solve to get A = 1/2
  linarith