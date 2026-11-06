import Mathlib

theorem algebra_234776 (a b c : ℝ) (ha : a^3-2020*a+1010=0) (hb : b^3-2020*b+1010=0)
    (hc : c^3-2020*c+1010=0) (habc : a≠b ∧ a≠c ∧ b≠c) :
    1/a+1/b+1/c=2 := by

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith

  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    nlinarith

  have hc1 : c ≠ 0 := by
    by_contra h
    rw [h] at hc
    nlinarith

  have eq1 : a^2 + a * b + b^2 = 2020 := by
    have eq2 : (a - b) * (a^2 + a * b + b^2 - 2020) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply habc.1
        linarith
      ), sq_nonneg (a - b), sq_nonneg (a + b)]
    cases (mul_eq_zero.mp eq2) with
    | inl h1 =>
      exfalso
      apply habc.1
      linarith
    | inr h2 =>
      linarith

  have eq2 : a^2 + a * c + c^2 = 2020 := by
    have eq3 : (a - c) * (a^2 + a * c + c^2 - 2020) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show a - c ≠ 0 by
        intro h
        apply habc.2.1
        linarith
      ), sq_nonneg (a - c), sq_nonneg (a + c)]
    cases (mul_eq_zero.mp eq3) with
    | inl h1 =>
      exfalso
      apply habc.2.1
      linarith
    | inr h2 =>
      linarith

  have eq3 : b^2 + b * c + c^2 = 2020 := by
    have eq4 : (b - c) * (b^2 + b * c + c^2 - 2020) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show b - c ≠ 0 by
        intro h
        apply habc.2.2
        linarith
      ), sq_nonneg (b - c), sq_nonneg (b + c)]
    cases (mul_eq_zero.mp eq4) with
    | inl h1 =>
      exfalso
      apply habc.2.2
      linarith
    | inr h2 =>
      linarith

  have eq4 : a + b + c = 0 := by
    have eq5 : (b - c) * (a + b + c) = 0 := by
      have eq6 : a * b + b ^ 2 - a * c - c ^ 2 = 0 := by
        nlinarith [eq1, eq2]
      have eq7 : a * (b - c) + (b - c) * (b + c) = 0 := by
        nlinarith [eq6]
      have eq8 : (b - c) * (a + b + c) = 0 := by
        linarith [eq7]
      exact eq8
    cases (mul_eq_zero.mp eq5) with
    | inl h1 =>
      exfalso
      apply habc.2.2
      linarith
    | inr h2 =>
      linarith

  have eq5 : a * b + a * c + b * c = -2020 := by
    have eq5c : c = -a - b := by linarith
    rw [eq5c]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg ((-a - b) - b), sq_nonneg ((-a - b) - a), sq_nonneg (b - a), sq_nonneg (b - (-a - b)), sq_nonneg (a - (-a - b)), sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply habc.1
      linarith
    ), sq_pos_of_ne_zero (show a - c ≠ 0 by
      intro h
      apply habc.2.1
      linarith
    ), sq_pos_of_ne_zero (show b - c ≠ 0 by
      intro h
      apply habc.2.2
      linarith
    )]

  have eq6 : a * b * c = -1010 := by
    have h1 : c ^ 3 - 2020 * c + 1010 = 0 := hc
    have eq7c : c = -a - b := by linarith
    rw [eq7c] at h1 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg ((-a - b) - b), sq_nonneg ((-a - b) - a), sq_nonneg (b - a), sq_nonneg (b - (-a - b)), sq_nonneg (a - (-a - b)), sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply habc.1
      linarith
    ), sq_pos_of_ne_zero (show a - c ≠ 0 by
      intro h
      apply habc.2.1
      linarith
    ), sq_pos_of_ne_zero (show b - c ≠ 0 by
      intro h
      apply habc.2.2
      linarith
    )]

  have eq7 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by
    field_simp [ha1, hb1, hc1]
    <;> ring_nf

  rw [eq7]
  rw [eq5, eq6]
  all_goals norm_num