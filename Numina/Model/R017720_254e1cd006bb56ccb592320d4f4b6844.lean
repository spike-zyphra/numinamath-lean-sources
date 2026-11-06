import Mathlib

theorem algebra_1017 (a b c d : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
(hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : a^2 - 10 * c * a - 11 * d = 0) (h2 : b^2 - 10 * c * b - 11 * d = 0) (h3 : c^2 - 10 * a * c - 11 * b = 0) (h4 : d^2 - 10 * a * d - 11 * b = 0) :
Real.sqrt ((a + b + c + d) / 10) = 11 := by

  have eq1 : a + b = 10 * c := by
    have h1' : a^2 - 10 * c * a - 11 * d = 0 := h1
    have h2' : b^2 - 10 * c * b - 11 * d = 0 := h2
    have h5 : (a - b) * (a + b - 10 * c) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7 
    · -- a - b = 0
      exfalso
      apply ha
      linarith
    · -- a + b - 10 * c = 0
      linarith

  have eq2 : c + d = 10 * a := by 
    have h3' : c^2 - 10 * a * c - 11 * b = 0 := h3
    have h4' : d^2 - 10 * a * d - 11 * b = 0 := h4
    have h6 : (c - d) * (c + d - 10 * a) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- c - d = 0
      exfalso
      apply hf
      linarith
    · -- c + d - 10 * a = 0
      linarith

  have eq3 : a + b + c + d = 10 * (a + c) := by 
    nlinarith [eq1, eq2]

  have eq7 : c^2 - 10 * a * c + 11 * a - 110 * c = 0 := by
    have eq4' : d^2 - 10 * a * d - 11 * b = 0 := h4
    have eq4 : b = 10 * c - a := by
      have h1' : a + b = 10 * c := eq1
      linarith
    have eq5 : d = 10 * a - c := by
      have h2' : c + d = 10 * a := eq2
      linarith
    rw [eq4, eq5] at eq4'
    nlinarith

  have eq8 : a + c = 121 := by 
    have eq4 : a * (a - 10 * c) - 11 * (10 * a - c) = 0 := by
      have h1' : a^2 - 10 * c * a - 11 * d = 0 := h1
      have eq5 : d = 10 * a - c := by
        nlinarith [eq1, eq2]
      rw [eq5] at h1'
      nlinarith
    by_cases h10 : a - c = 0
    · -- Assume a - c = 0, so a = c
      exfalso
      apply hb
      linarith
    · -- a - c ≠ 0
      have h9 : a + c = 121 := by 
        apply (mul_left_inj' h10).mp
        nlinarith [sq_pos_of_ne_zero (show a - c ≠ 0 by assumption), sq_nonneg (a - c), sq_nonneg (c - a), sq_nonneg (a + c - 121)]
      linarith

  have eq7' : a + b + c + d = 1210 := by
    rw [eq3]
    nlinarith [eq8]

  have eq8' : Real.sqrt ((a + b + c + d) / 10) = 11 := by
    rw [eq7']
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  exact eq8'