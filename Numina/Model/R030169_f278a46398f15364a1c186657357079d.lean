import Mathlib

theorem algebra_165142 : Set.Infinite {x : ℚ | ∃ q : ℚ, q^2 = x^2 + x + 1} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ((↑n : ℚ) ^ 2 - 4) / (4 * ((↑n : ℚ) + 1)))
  · -- Show f is injective
    intro n m h
    have h_eq : ((↑n : ℚ) ^ 2 - 4) / (4 * ((↑n : ℚ) + 1)) = ((↑m : ℚ) ^ 2 - 4) / (4 * ((↑m : ℚ) + 1)) := by
      simpa using h
    have h_eq2 : ((↑n : ℚ) ^ 2 - 4) * (4 * ((↑m : ℚ) + 1)) = ((↑m : ℚ) ^ 2 - 4) * (4 * ((↑n : ℚ) + 1)) := by
      have h1 : ((↑n : ℚ) + 1) ≠ 0 := by
        have hn1 : (↑n : ℚ) ≥ 0 := by
          exact_mod_cast show (0 : ℕ) ≤ n by omega
        nlinarith
      have h2 : ((↑m : ℚ) + 1) ≠ 0 := by
        have hm1 : (↑m : ℚ) ≥ 0 := by
          exact_mod_cast show (0 : ℕ) ≤ m by omega
        nlinarith
      field_simp at h_eq ⊢
      nlinarith
    have h_eq3 : ((↑n : ℚ) - (↑m : ℚ)) * ((↑n * (↑m) : ℚ) + (↑n + (↑m) : ℚ) + 4) = 0 := by
      ring_nf at h_eq2 ⊢
      nlinarith
    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · 
      have : (↑n : ℚ) = (↑m : ℚ) := by
        linarith
      have : n = m := by
        exact_mod_cast this
      omega
    · 
      have h_eq6 : ((↑n * (↑m) : ℚ) + (↑n + (↑m) : ℚ) + 4) = (0 : ℚ) := by
        linarith
      have h_eq7 : (↑n * (↑m) + ↑n + ↑m + 4 : ℚ) = (0 : ℚ) := by 
        linarith
      have h_eq8 : (↑n : ℚ) ≥ (0 : ℚ) := by 
        have hn1 : (↑n : ℚ) ≥ 0 := by 
          exact_mod_cast show (0 : ℕ) ≤ n by omega
        linarith
      have h_eq9 : (↑m : ℚ) ≥ (0 : ℚ) := by 
        have hm1 : (↑m : ℚ) ≥ 0 := by 
          exact_mod_cast show (0 : ℕ) ≤ m by omega
        linarith
      have h_eq10 : ((↑n : ℚ) * (↑m : ℚ) + (↑n : ℚ) + (↑m : ℚ) + 4) ≥ (4 : ℚ) := by
        nlinarith [mul_nonneg (show (0 : ℚ) ≤ (↑n : ℚ) by linarith) (show (0 : ℚ) ≤ (↑m : ℚ) by linarith)]
      nlinarith
  · -- Show all elements in the image of f are in the set
    intro n
    have h_eq2 : ∃ q : ℚ, q ^ 2 = (((↑n : ℚ) ^ 2 - 4) / (4 * ((↑n : ℚ) + 1)) ) ^ 2 + (((↑n : ℚ) ^ 2 - 4) / (4 * ((↑n : ℚ) + 1)) ) + 1 := by
      use ((↑n + 1 : ℚ) ^ 2 + 3) / (4 * ((↑n + 1 : ℚ) : ℚ))
      have h1 : ((↑n + 1 : ℚ) : ℚ) ≠ 0 := by
        have hn1 : (↑n : ℚ) ≥ 0 := by
          exact_mod_cast show (0 : ℕ) ≤ n by omega
        nlinarith
      field_simp [h1]
      ring
    simpa using h_eq2