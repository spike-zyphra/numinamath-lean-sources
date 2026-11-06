import Mathlib

theorem algebra_324954 (n : ℕ) (h₀ : n > 0) (h₁ : (1 / n : ℚ) + (1 / (n + 1 : ℚ)) + (1 / (n + 2 : ℚ)) = 47 / 60) :
    n = 3 := by 
  have h3 : n ≥ 1 := by linarith
  have h4 : (n : ℚ) ≥ (1 : ℚ) := by
    exact_mod_cast h3
  have eq1 : (1 / (n : ℚ) : ℚ) + (1 / ((n + 1 : ℚ)) : ℚ) + (1 / ((n + 2 : ℚ)) : ℚ) = ( ((n + 1 : ℚ) * (n + 2 : ℚ) + (n : ℚ) * (n + 2 : ℚ) + (n : ℚ) * (n + 1 : ℚ)) ) / ( (n : ℚ) * (n + 1 : ℚ) * (n + 2 : ℚ) ) := by
    field_simp
    <;> ring
  rw [eq1] at h₁
  have h8 : ((n + 1 : ℚ) * (n + 2 : ℚ) + (n : ℚ) * (n + 2 : ℚ) + (n : ℚ) * (n + 1 : ℚ)) * 60 = 47 * ( (n : ℚ) * (n + 1 : ℚ) * (n + 2 : ℚ) ) := by
    field_simp [(show (n : ℚ) ≠ 0 by positivity), (show (n + 1 : ℚ) ≠ 0 by positivity), (show (n + 2 : ℚ) ≠ 0 by positivity)] at h₁ ⊢
    nlinarith
  have h9 : ((n + 1 : ℕ) * (n + 2 : ℕ) + (n : ℕ) * (n + 2 : ℕ) + (n : ℕ) * (n + 1 : ℕ)) * 60 = 47 * ( (n : ℕ) * (n + 1 : ℕ) * (n + 2 : ℕ) ) := by 
    exact_mod_cast h8
  have h4' : n ≤ 10 := by
    nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ)), sq_nonneg ((n + 2 : ℕ)), sq_pos_of_pos (show (n : ℕ) > 0 by linarith)]
  interval_cases n <;> omega