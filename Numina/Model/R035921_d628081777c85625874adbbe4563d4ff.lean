import Mathlib

theorem algebra_228237 {a : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 + a * x1 + 2 * a = 0 ∧ x2^2 + a * x2 + 2 * a = 0 ∧
    x1^2 + x2^2 = 21) : a = -3 := by
  rcases h with ⟨x1, x2, h_ne, h1, h2, h3⟩
  have eq1 : (x1 - x2) * (x1 + x2 + a) = 0 := by 
    nlinarith
  cases (mul_eq_zero.mp eq1) with 
  | inl h4 => 
    exfalso
    apply h_ne
    linarith
  | inr h5 =>
    have h_sum : x1 + x2 = -a := by linarith
    have eq2 : (a - 7) * (a + 3) = 0 := by
      nlinarith [h1, h2, h3, h_sum, sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h'
        apply h_ne
        linarith
      )]
    cases (mul_eq_zero.mp eq2) with
    | inl h5 =>
      -- Here a = 7. But discriminant of equation will be negative.
      have h_a : a = 7 := by linarith
      subst a 
      norm_num at h1 h2 
      nlinarith [sq_nonneg (x1), sq_nonneg (x2), sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h'
        apply h_ne
        linarith
      )
      ]
    | inr h6 =>
      linarith