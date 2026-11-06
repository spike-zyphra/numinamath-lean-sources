import Mathlib

theorem algebra_287174 (n m : ℕ) (h₀ : n + m = 315) (h₁ : (60 / 100 : ℝ) * n + (1 / 3 : ℝ) * m = (1 / 2 : ℝ) * (n + m)) :
    n = 90 ∧ m = 225 := by
  have eq1 : (n : ℝ) + (m : ℝ) = 315 := by
    exact_mod_cast h₀
  have eq2 : (60 / 100 : ℝ) * (n : ℝ) + (1 / 3 : ℝ) * (m : ℝ) = (1 / 2 : ℝ) * ((n : ℝ) + (m : ℝ)) := by
    linarith [h₁]
  rw [show (n : ℝ) + (m : ℝ) = 315 by linarith [eq1] ] at eq2
  have eq3 : (n : ℝ) = (315 : ℝ) - (m : ℝ) := by 
    linarith [eq1]
  rw [eq3] at eq2
  norm_num at eq2
  have eq5 : (m : ℝ) ≥ 0 := by 
    exact_mod_cast show (m : ℕ) ≥ 0 by omega
  have : (m : ℝ) ≤ (315 : ℝ) := by 
    nlinarith [eq1, eq5]
  have : m ≤ 315 := by
    by_contra h
    push_neg at h
    have : m > 315 := by omega
    have : (m : ℝ) > (315 : ℝ) := by 
      exact_mod_cast this
    nlinarith
  interval_cases m <;> norm_num at eq2 <;> norm_num at eq1 <;> omega