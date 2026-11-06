import Mathlib

theorem algebra_315324 (a b c d : ℝ) (h₀ : a = (b + c + d)^3) (h₁ : b = (a + c + d)^3)
    (h₂ : c = (a + b + d)^3) (h₃ : d = (a + b + c)^3) :
    a = b ∧ b = c ∧ c = d := by
  have eq1 : a - b = 0 := by
    have eq1 : a - b = (b + c + d) ^ 3 - (a + c + d) ^ 3 := by
      linarith 
    have eq2 : (b + c + d) ^ 3 - (a + c + d) ^ 3 = (b - a) * ((b + c + d) ^ 2 + (b + c + d) * (a + c + d) + (a + c + d) ^ 2) := by
      ring
    rw [eq2] at eq1
    have eq3 : (a - b) * (1 + ((b + c + d) ^ 2 + (b + c + d) * (a + c + d) + (a + c + d) ^ 2)) = 0 := by 
      linarith 
    cases' (mul_eq_zero.1 eq3) with eq4 eq5
    · -- Case where `a - b = 0` 
      linarith 
    · -- Case where `1 + ... = 0` 
      nlinarith [sq_nonneg (b + c + d), sq_nonneg (a + c + d), sq_nonneg ( (b + c + d) + (a + c + d) ), sq_nonneg ( (b + c + d) - (a + c + d) ) ]
  have h7 : a = b := by linarith [eq1]
  have eq2 : b - c = 0 := by 
    have eq2 : b - c = (a + c + d) ^ 3 - (a + b + d) ^ 3 := by 
      linarith 
    have eq3 : (a + c + d) ^ 3 - (a + b + d) ^ 3 = (c - b) * ((a + c + d) ^ 2 + (a + c + d) * (a + b + d) + (a + b + d) ^ 2) := by 
      ring 
    rw [eq3] at eq2 
    have eq4 : (b - c) * (1 + ((a + c + d) ^ 2 + (a + c + d) * (a + b + d) + (a + b + d) ^ 2)) = 0 := by 
      linarith 
    cases' (mul_eq_zero.1 eq4) with eq5 eq6
    · -- Case where `b - c = 0` 
      linarith 
    · -- Case where `1 + ... = 0` 
      nlinarith [ sq_nonneg (a + c + d), sq_nonneg (a + b + d), sq_nonneg ((a + c + d) + (a + b + d)), sq_nonneg ((a + c + d) - (a + b + d) ) ]
  have h8 : b = c := by linarith [eq2]
  have eq3 : c - d = 0 := by 
    have eq3 : c - d = (a + b + d) ^ 3 - (a + b + c) ^ 3 := by 
      linarith 
    have eq4 : (a + b + d) ^ 3 - (a + b + c) ^ 3 = (d - c) * ((a + b + d) ^ 2 + (a + b + d) * (a + b + c) + (a + b + c) ^ 2) := by 
      ring 
    rw [eq4] at eq3 
    have eq5 : (c - d) * (1 + ((a + b + d) ^ 2 + (a + b + d) * (a + b + c) + (a + b + c) ^ 2)) = 0 := by 
      linarith 
    cases' (mul_eq_zero.1 eq5) with eq6 eq7
    · -- Case where `c - d = 0` 
      linarith 
    · -- Case where `1 + ... = 0` 
      nlinarith [ sq_nonneg (a + b + d), sq_nonneg (a + b + c), sq_nonneg ((a + b + d) + (a + b + c)), sq_nonneg ((a + b + d) - (a + b + c) ) ]
  have h9 : c = d := by linarith [eq3]
  exact ⟨h7, h8, h9⟩