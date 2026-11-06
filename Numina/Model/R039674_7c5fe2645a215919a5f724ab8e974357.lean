import Mathlib

theorem algebra_6534 {x y z : ℝ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x)
    (h1 : x^3 + 20*y + 20*z = 20) (h2 : y^3 + 20*z + 20*x = 20) (h3 : z^3 + 20*x + 20*y = 20) :
    x^2 + y^2 + z^2 = 40 := by
  rcases h with ⟨hx1, hy1, hz1⟩
  have eq1 : x^2 + x * y + y^2 = 20 := by 
    have eq2 : (x - y) * (x^2 + x * y + y^2 - 20) = 0 := by
      have h4 : x^3 + 20 * y + 20 * z - (y^3 + 20 * z + 20 * x) = 0 := by linarith
      ring_nf at h4 ⊢
      nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
        intro h'
        apply hy1
        linarith
      ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
        intro h'
        apply hz1
        linarith
      ), sq_nonneg (x - y), sq_nonneg (y - x), sq_nonneg (x - z), sq_nonneg (z - x), sq_nonneg (y - z), sq_nonneg (z - y)]
    cases (mul_eq_zero.1 eq2) with
    | inl h4 =>
      exfalso
      apply hx1
      linarith
    | inr h5 =>
      linarith
  -- Subtract the second and third equations
  have eq2 : y^2 + y * z + z^2 = 20 := by
    have eq2 : (y - z) * (y^2 + y * z + z^2 - 20) = 0 := by
      have h4 : y^3 + 20 * z + 20 * x - (z^3 + 20 * x + 20 * y) = 0 := by linarith
      ring_nf at h4 ⊢
      nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
        intro h'
        apply hy1
        linarith
      ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
        intro h'
        apply hz1
        linarith
      ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
        intro h'
        apply hy1
        linarith
      ), sq_nonneg (y - z), sq_nonneg (z - y), sq_nonneg (y - x), sq_nonneg (x - y), sq_nonneg (z - x), sq_nonneg (x - z)]
    cases (mul_eq_zero.1 eq2) with
    | inl h4 =>
      exfalso
      apply hy1
      linarith
    | inr h5 =>
      linarith
  -- Subtract the first and third equations
  have eq3 : z^2 + z * x + x^2 = 20 := by
    have eq2 : (z - x) * (z^2 + z * x + x^2 - 20) = 0 := by
      have h4 : x^3 + 20 * y + 20 * z - (z^3 + 20 * x + 20 * y) = 0 := by linarith
      ring_nf at h4 ⊢
      nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
        intro h'
        apply hy1
        linarith
      ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
        intro h'
        apply hz1
        linarith
      ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
        intro h'
        apply hz1
        linarith
      ), sq_nonneg (z - x), sq_nonneg (x - z), sq_nonneg (z - y), sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (y - x)]
    cases (mul_eq_zero.1 eq2) with
    | inl h4 =>
      exfalso
      apply hz1
      linarith
    | inr h5 =>
      linarith
  -- Show that x + y + z = 0
  have h4 : x + y + z = 0 := by
    have eq5 : (x - y) * (x + y + z) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
        intro h'
        apply hy1
        linarith
      ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
        intro h'
        apply hz1
        linarith
      )]
    cases (mul_eq_zero.1 eq5) with
    | inl h5 =>
      exfalso
      apply hx1
      linarith
    | inr h6 =>
      linarith
  -- Now we can compute x^2 + y^2 + z^2.
  have h5 : x * y + y * z + z * x = -20 := by
    have h6 : (x + y + z) ^ 2 = 0 := by
      rw [h4]
      norm_num
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
    intro h'
    apply hx1
    linarith
  ), sq_pos_of_ne_zero (show (y - z : ℝ) ≠ 0 by
    intro h'
    apply hy1
    linarith
  ), sq_pos_of_ne_zero (show (z - x : ℝ) ≠ 0 by
    intro h'
    apply hz1
    linarith
  )]