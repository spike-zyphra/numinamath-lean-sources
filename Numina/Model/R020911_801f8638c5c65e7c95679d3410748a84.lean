import Mathlib

theorem algebra_286724 {n : ℕ} (hn : n ≥ 3) (a b c : ℝ)
    (ha : a = (n - 2) * b + c) (hb : b = (n - 1) * c + 7)
    (hc : c = (n - 1) * b - 7) (h : (n - 2) * b + c = 7 * (n - 1)) :
    n = 7 := by
  -- Convert hn to real numbers
  have h1 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn
  -- Express b from hb and hc
  have eq2 : b * (1 - ((n : ℝ) - 1)^2) = 7 * (- ((n : ℝ)) + 2) := by
    have eq_b : b = (n - 1) * c + 7 := hb
    have eq_c : c = (n - 1) * b - 7 := hc
    rw [eq_c] at eq_b
    -- Simplify the equation b = (n - 1) * ((n - 1) * b - 7) + 7
    nlinarith
  -- Express b from h and hc
  have eq3 : b * (2 * ((n : ℝ)) - 3) = 7 * ((n : ℝ)) := by
    have h' : (↑n - 2) * b + c = 7 * (↑n - 1) := h
    have hc' : c = (↑n - 1) * b - 7 := hc
    rw [hc'] at h'
    -- Simplify (n - 2)*b + ((n - 1)*b - 7) = 7*(n - 1) to b*(2n - 3) = 7n
    nlinarith [sq_nonneg ((n : ℝ) - 2 : ℝ), sq_nonneg (b : ℝ)]
  -- Check denominator is non-zero
  have eq5_denom_ne_zero : 2 * (n : ℝ) - 3 ≠ 0 := by
    by_contra h_eq_zero
    have h2n3 : 2 * (n : ℝ) - 3 = (0 : ℝ) := by linarith
    have h_n_val : (n : ℝ) = (3 : ℝ)/2 := by linarith
    have h_n_nat : n = 1 := by
      have hn1 : (n : ℝ) = (3 : ℝ)/2 := h_n_val
      have hn1' : (2 * (n : ℝ)) = (3 : ℝ) := by linarith
      have hn2 : (2 * n : ℝ) = (3 : ℝ) := by norm_cast at hn1' ⊢
      have hn3 : 2 * n = 3 := by exact_mod_cast hn2
      omega
    nlinarith [h_n_nat, h1]
  have eq6 : b = (7 * ((n : ℝ))) / (2 * ((n : ℝ)) - 3) := by
    field_simp [eq5_denom_ne_zero]
    nlinarith
  -- Substitute eq6 into eq2
  have eq4 : ((7 * ((n : ℝ))) / (2 * ((n : ℝ)) - 3)) * (1 - ((n : ℝ) - 1)^2) = 7 * (- ((n : ℝ)) + 2) := by
    rw [eq6] at eq2
    exact_mod_cast eq2
  -- Simplify to polynomial equation
  have eq7 : (n : ℝ)^3 - 4 * (n : ℝ)^2 + 7 * (n : ℝ) - 6 = 0 := by
    field_simp [eq5_denom_ne_zero] at eq4
    nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) - 2)]
  -- Factor polynomial
  have eq8 : ((n : ℝ) - 2) * ((n : ℝ)^2 - 2 * (n : ℝ) + 3) = 0 := by
    nlinarith
  -- Show second factor is non-zero
  have eq9 : (n : ℝ)^2 - 2 * (n : ℝ) + 3 ≠ 0 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  -- Conclude n = 2
  have eq10 : (n : ℝ) = (2 : ℝ) := by
    cases' (mul_eq_zero.1 eq8) with h11 h12
    · linarith
    · -- Show the second factor can't be zero
      exfalso
      apply eq9
      exact h12
  -- Contradiction with n >= 3
  have eq11 : (n : ℝ) ≥ (3 : ℝ) := h1
  -- Convert eq10 back to natural number
  have eq12 : n = 2 := by
    exact_mod_cast eq10
  -- Contradiction and proof of the original goal
  omega