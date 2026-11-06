import Mathlib

theorem algebra_238020 {n S : ℕ} (h1 : 6 * n + 2 = S) (h2 : 7 * n - 3 = S) :
    n = 5 ∧ S = 32 := by
  have eq1 : S = 6 * n + 2 := by 
    omega

  have eq2 : S = 7 * n - 3 := by 
    omega

  have hn : n = 5 := by
    omega

  have hS : S = 32 := by
    rw [hn] at eq1
    omega

  exact ⟨hn, hS⟩