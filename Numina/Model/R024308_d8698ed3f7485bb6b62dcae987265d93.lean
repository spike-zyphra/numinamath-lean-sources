import Mathlib

theorem algebra_233418 {a b : ℝ} (ha : a^4 ≠ 0) (hb : b^4 ≠ 0)
    (h1 : 4 / a^4 - 2 / a^2 - 3 = 0) (h2 : b^4 + b^2 - 3 = 0) :
    (a^4 * b^4 + 4) / a^4 = 7 := by

  have eq1 : 3 * a^4 + 2 * a^2 - 4 = 0 := by
    have h1' : a^4 ≠ 0 := ha
    have eq1 : 4 / a^4 - 2 / a^2 - 3 = 0 := h1
    field_simp [show a ≠ 0 by 
      by_contra h
      have h' : a = 0 := by linarith
      rw [h'] at eq1
      norm_num [h'] at eq1 ⊢ 
    ] at eq1 ⊢
    nlinarith [sq_nonneg (a ^ 2), sq_pos_of_ne_zero ha, sq_nonneg (a), sq_nonneg (a^2), sq_nonneg (a^4)]

  have eq2 : b^4 = 3 - b^2 := by
    nlinarith

  have eq4 : (a^4 * b^4 + 4) / a^4 = b^4 + 4 / a^4 := by 
    field_simp [show a^4 ≠ 0 by exact ha, show a ≠ 0 by 
      by_contra h
      have h' : a = 0 := by linarith
      rw [h'] at h1
      norm_num [h'] at h1 ⊢ 
    ]
    <;> nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a ^ 4), sq_pos_of_ne_zero ha, sq_nonneg (a ^ 2), sq_nonneg (a)]

  rw [eq4]

  have h3 : 4 / a^4 = 3 + 2 / a^2 := by
    have h1' : a^4 ≠ 0 := ha
    have eq1 : 4 / a^4 - 2 / a^2 - 3 = 0 := h1
    field_simp [show a ≠ 0 by 
      by_contra h
      have h' : a = 0 := by linarith
      rw [h'] at eq1
      norm_num [h'] at eq1 ⊢ 
    ] at eq1 ⊢
    linarith [eq1, sq_pos_of_ne_zero ha]

  have h4 : 4 / a^2 = 3 * a^2 + 2 := by
    have eq1 : 3 * a^4 + 2 * a^2 - 4 = 0 := by assumption
    have ha1 : a ≠ 0 := by
      by_contra h
      have h' : a = 0 := by linarith
      rw [h'] at eq1
      norm_num [h'] at eq1 ⊢ 
    have h5 : a^2 ≠ 0 := by
      intro h'
      have h_eq : a = 0 := by
        nlinarith
      trivial -- contradiction
    have h6 : 4 / a^2 = 3 * a^2 + 2 := by
      field_simp [h5] at *
      nlinarith
    exact h6

  have h7 : b^4 + 4 / a^4 = 7 := by
    have eq3 : 4 / a^4 = 3 + 2 / a^2 := h3
    have eq8 : b^4 = 3 - b^2 := eq2
    have h5' : 2 / a^2 = 1 + b^2 := by
      have h4' : 4 / a^2 = 3 * a^2 + 2 := h4
      field_simp [(show (a: ℝ) ≠ 0 by 
        by_contra h
        have h' : a = 0 := by linarith
        rw [h'] at eq1
        norm_num [h'] at eq1 ⊢ 
      )] at h4' ⊢
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (a * b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 4 - a ^ 2)]
    rw [eq3, eq8]
    nlinarith [h5']
  exact_mod_cast h7