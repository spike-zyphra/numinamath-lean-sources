import Mathlib

theorem algebra_111441 {n : ℕ} (hn : n ≠ 0) : 2 * n - 1 / (n ^ 5 : ℚ) = 3 - 2 / n ↔ n = 1 := by
  constructor
  · -- Assume the equation holds, prove n = 1
    intro h_eq
    have eq1 : (n : ℚ) > 0 := by
      exact_mod_cast show (n : ℕ) > 0 from Nat.pos_of_ne_zero hn
    have eq2 : (n : ℚ) ≥ 1 := by
      exact_mod_cast show n ≥ 1 from Nat.pos_of_ne_zero hn
    have eq3 : (2 * (n : ℚ) - 1 / ((n : ℚ) ^ 5)) = 3 - 2 / (n : ℚ) := by
      simpa using h_eq
    have eq4 : 2 * ((n : ℚ) ^ 6) - 3 * ((n : ℚ) ^ 5) + 2 * ((n : ℚ) ^ 4) - 1 = 0 := by
      have h1 : (n : ℚ) ^ 5 > 0 := by positivity
      field_simp at eq3 ⊢
      nlinarith [sq_nonneg ((n : ℚ) ^ 2), sq_nonneg ((n : ℚ) ^ 3), sq_nonneg ((n : ℚ) - 1), sq_nonneg ((n : ℚ) ^ 4)]
    have eq5 : n ≤ 1 := by
      by_contra h
      push_neg at h
      have h2 : n ≥ 2 := by
        omega
      have h3 : (n : ℚ) ≥ 2 := by
        exact_mod_cast h2
      nlinarith [sq_nonneg ((n : ℚ) ^ 2), sq_nonneg ((n : ℚ) ^ 3), sq_nonneg ((n : ℚ) - 1), sq_nonneg ((n : ℚ) ^ 4), sq_nonneg ((n : ℚ) ^ 5), sq_nonneg ((n : ℚ) ^ 6)]
    have eq6 : n = 1 := by
      omega
    tauto
  · -- Assume n = 1, prove the equation
    intro h_eq
    rw [h_eq]
    norm_num