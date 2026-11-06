import Mathlib

theorem algebra_201463 {a b : ℝ} (ha : a * b ≠ 2) (f : ℝ → ℝ)
    (hf : ∀ x, f x = (b * x + 1) / (2 * x + a)) (k : ℝ)
    (h : ∀ x, f x * f (1 / x) = k) :
    k = 1 / 4 := by
  have eq1 := h 1
  norm_num [hf] at eq1
  have eq2 := h 2
  norm_num [hf] at eq2
  have eq3 := h (-1)
  norm_num [hf] at eq3
  have eq4 := h (-a / 2)
  norm_num [hf] at eq4
  have eq5 := h a
  norm_num [hf] at eq5
  have eq6 := h (1 / a)
  norm_num [hf] at eq6
  have eq7 := h (-2)
  norm_num [hf] at eq7
  have eq8 := h (1)
  norm_num [hf] at eq8
  field_simp [(show (2 + a ≠ 0) by
    -- can't prove easily, so need to work with equational constraints.
    by_contra h'
    -- derivative yields contradiction
    have : 2 + a = 0 := by linarith
    rw [show a = -2 by linarith] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals nlinarith [sq_pos_of_ne_zero (show a * b - 2 ≠ 0 by
      by_contra h'
      have : a * b = 2 := by linarith
      contradiction
    ), sq_nonneg (a * b - 2)]
  ), (show (4 + a ≠ 0) by
    by_contra h'
    -- derivative yields contradiction
    have : 4 + a = 0 := by linarith
    rw [show a = -4 by linarith] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals nlinarith [sq_pos_of_ne_zero (show a * b - 2 ≠ 0 by
      by_contra h'
      have : a * b = 2 := by linarith
      contradiction
    ), sq_nonneg (a * b - 2)]
  ), (show (1 + a ≠ 0) by
    by_contra h'
    -- derivative yields contradiction
    have : 1 + a = 0 := by linarith
    rw [show a = -1 by linarith] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals nlinarith [sq_pos_of_ne_zero (show a * b - 2 ≠ 0 by
      by_contra h'
      have : a * b = 2 := by linarith
      contradiction
    ), sq_nonneg (a * b - 2)]
  ), (show (a ≠ 0) by
    by_contra h'
    -- derivative yields contradiction
    have : a = 0 := by linarith
    rw [this] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
    all_goals nlinarith [sq_nonneg (a * b - 2), sq_pos_of_ne_zero (show a * b - 2 ≠ 0 by
      by_contra h'
      have : a * b = 2 := by linarith
      contradiction
    )]
  ) ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  nlinarith [sq_nonneg (a * b - 2), sq_nonneg (a ^ 2 - 4), sq_nonneg (a * b), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
    sq_pos_of_ne_zero (show a * b - 2 ≠ 0 by
      intro h'
      have h6 : a * b = 2 := by linarith
      contradiction
    )
  ]