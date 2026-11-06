import Mathlib

theorem algebra_194278 {b : ℕ} (hb : b ≠ 0) (c : ℤ) (hc : c ≠ 0)
    (h : c / 6 = (b - 4 : ℝ) / (b + 46 + b - 4)) :
    c = 2 := by
  have h1 : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have eq1 : (c : ℝ) / 6 = ((b - 4) : ℝ) / (b + 46 + b - 4) := by
    exact_mod_cast h
  have total_balls : ((b : ℝ) + 46 + (b : ℝ) - 4) = (2 * (b : ℝ) + 42) := by ring
  rw [total_balls] at eq1
  have eq2 : (c : ℝ) * (2 * (b : ℝ) + 42) = 6 * ((b : ℝ) - 4) := by
    field_simp at eq1 ⊢
    linarith
  have eq3 : c * (2 * b + 42) = 6 * (b - 4) := by
    exact_mod_cast eq2
  have h4 : b ≥ 1 := by 
    by_contra h
    push_neg at h
    have : b = 0 := by omega
    contradiction
  have h8 : c ≤ 6 := by 
    nlinarith [show 2 * b + 42 ≥ 44 from by omega,
        show (b : ℤ) ≥ 1 by omega, 
        sq_nonneg ( (c : ℤ) - 3 ) ]
  have h9 : c ≥ -4 := by 
    nlinarith [show 2 * b + 42 ≥ 44 from by omega, 
        show (b : ℤ) ≥ 1 by omega, 
        sq_nonneg ( (c : ℤ) + 2 ) ]
  interval_cases c <;> omega