import Mathlib

theorem algebra_157833 {a b : ℝ} (h₀ : a ≠ b) (h₁ : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) = 2 / (a * b + 1)) :
    1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 2 / (a * b + 1) = 2 := by

  have eq1 : (a ^ 2 + b ^ 2 + 2) * (a * b + 1) = 2 * (a ^ 2 + 1) * (b ^ 2 + 1) := by
    have h2 : a ^ 2 + 1 ≠ 0 := by
      by_contra h
      have : a ^ 2 = -1 := by linarith
      have h3 : a ^ 2 ≥ 0 := sq_nonneg a
      nlinarith
    have h3 : b ^ 2 + 1 ≠ 0 := by
      by_contra h
      have : b ^ 2 = -1 := by linarith
      have h3 : b ^ 2 ≥ 0 := sq_nonneg b
      nlinarith
    have h4 : a * b + 1 ≠ 0 := by
      by_contra h
      have h5 : 2 / (a * b + 1) = 0 := by
        rw [h]
        norm_num
      have h6 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) = 0 := by linarith [h₁, h5]
      have h7 : 1 / (a ^ 2 + 1) > 0 := by
        apply div_pos
        norm_num
        nlinarith [sq_nonneg a, sq_nonneg b]
      have h8 : 1 / (b ^ 2 + 1) > 0 := by
        apply div_pos
        norm_num
        nlinarith [sq_nonneg a, sq_nonneg b]
      nlinarith [h6, h7, h8]
    field_simp [(show a ^ 2 + 1 ≠ 0 by assumption), (show b ^ 2 + 1 ≠ 0 by assumption), (show a * b + 1 ≠ 0 by assumption)] at h₁ ⊢
    nlinarith [h₁]

  have eq2 : a * b = 1 := by
    have eq3 : (a - b) ^ 2 * (a * b - 1) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        intro h'
        apply h₀
        linarith
      ), sq_nonneg (a + b), sq_nonneg (a - b)]
    cases' (mul_eq_zero.mp eq3) with eq4 eq5
    · -- (a - b) ^ 2 = 0, contradiction
      have : (a - b) ^ 2 = 0 := by
        linarith
      have : a - b = 0 := by
        apply pow_eq_zero 
        exact this
      have : a = b := by linarith
      contradiction
    · -- a * b - 1 = 0
      linarith

  have eq3 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) = 1 := by
    have h8 : a * b = 1 := eq2
    have h9 : b ≠ 0 := by
      by_contra h
      have : a * b = 0 := by
        rw [h]
        norm_num
      nlinarith
    have h10 : a ≠ 0 := by
      by_contra h
      have : a * b = 0 := by
        rw [h]
        norm_num
      nlinarith
    field_simp [(show a ^ 2 + 1 ≠ 0 by
      by_contra h
      have : a ^ 2 = -1 := by linarith
      have h3 : a ^ 2 ≥ 0 := sq_nonneg a
      nlinarith
    ), (show b ^ 2 + 1 ≠ 0 by
      by_contra h
      have : b ^ 2 = -1 := by linarith
      have h3 : b ^ 2 ≥ 0 := sq_nonneg b
      nlinarith
    ), (show b ≠ 0 by assumption), (show a ≠ 0 by assumption)]
    nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b)]


  have eq4 : 2 / (a * b + 1) = 1 := by
    have h8 : a * b = 1 := eq2
    have h9 : a * b + 1 = 2 := by linarith
    rw [h9]
    norm_num

  calc
    1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 2 / (a * b + 1) = (1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1)) + 2 / (a * b + 1) := by ring
    _ = 1 + 1 := by rw [eq3, eq4]
    _ = 2 := by norm_num