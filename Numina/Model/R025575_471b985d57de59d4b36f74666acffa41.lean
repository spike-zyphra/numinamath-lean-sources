import Mathlib

theorem algebra_195115 (n : ℕ) (hn : n ≠ 0) : 2 * n - 1 / (n ^ 5 : ℚ) = 3 - 2 / n ↔ n = 1 := by
  constructor
  · -- Forward direction: if equation holds, then n=1
    intro h_eq
    have h1 : (n : ℚ) ≠ 0 := by
      exact_mod_cast show n ≠ 0 by exact hn
    have eq1 : (2 * (↑n : ℚ) - 1 / (↑n ^ 5 : ℚ) ) = (3 - 2 / (↑n : ℚ)) := by
      simpa using h_eq
    -- clear denominators
    have eq2 : 2 * ((↑n : ℚ) ^ 6) + 2 * ((↑n : ℚ) ^ 4) - 3 * ((↑n : ℚ) ^ 5) - 1 = 0 := by
      have eq4 : (2 * (↑n : ℚ) - 1 / (↑n ^ 5 : ℚ) ) = (3 - 2 / (↑n : ℚ)) := by
        simpa using h_eq
      have eq5 : (2 * (↑n : ℚ) - 1 / (↑n ^ 5 : ℚ) ) * (↑n ^ 5) = (3 - 2 / (↑n : ℚ)) * (↑n ^ 5) := by
        rw [eq4]
      have eq6 : (2 * (↑n : ℚ) - 1 / (↑n ^ 5 : ℚ) ) * (↑n ^ 5) = 2 * ((↑n : ℚ) ^ 6) - 1 := by
        field_simp [h1]
        <;> ring
      have eq7 : (3 - 2 / (↑n : ℚ)) * (↑n ^ 5) = 3 * ((↑n : ℚ) ^ 5) - 2 * ((↑n : ℚ) ^ 4) := by
        field_simp [h1]
        <;> ring
      rw [eq6, eq7] at eq5
      linarith
    -- factor the polynomial
    have eq3 : (↑n : ℚ) = 1 := by
      have h2 : 2 * ((↑n : ℚ) ^ 6) + 2 * ((↑n : ℚ) ^ 4) - 3 * ((↑n : ℚ) ^ 5) - 1 = 0 := eq2
      have h3 : ((↑n : ℚ) - 1) * (2 * ((↑n : ℚ) ^ 5) - ((↑n : ℚ) ^ 4) + ((↑n : ℚ) ^ 3) + ((↑n : ℚ) ^ 2) + ((↑n : ℚ)) + 1) = 0 := by
        nlinarith [sq_nonneg ((↑n : ℚ) ^ 2 - (↑n : ℚ)), sq_nonneg ((↑n : ℚ) ^ 3 - (↑n : ℚ)), sq_nonneg ((↑n : ℚ) - 1), sq_nonneg ((↑n : ℚ) ^ 2 - 1)]
      cases (mul_eq_zero.1 h3) with
      | inl h4 =>
        have h4' : (↑n : ℚ) = 1 := by linarith
        exact_mod_cast h4'
      | inr h5 =>
        -- show the second factor is not zero
        nlinarith [sq_nonneg ((↑n : ℚ) ^ 2 - (↑n : ℚ)), sq_nonneg ((↑n : ℚ) ^ 3 - (↑n : ℚ)), sq_nonneg ((↑n : ℚ) - 1), sq_nonneg ((↑n : ℚ) ^ 2 - 1), sq_pos_of_pos (show (↑n : ℚ) > 0 by positivity)]
    have h2 : (↑n : ℚ) = 1 := eq3
    have h3 : (n : ℚ) = 1 := by simpa using h2
    have h4 : n = 1 := by
      exact_mod_cast h3
    exact h4
  · -- Backward direction: if n=1, then equation holds
    intro h_eq
    rw [h_eq]
    norm_num