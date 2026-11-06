import Mathlib

theorem number_theory_216987 (n : ℕ) :
    (n + 2)^3 ≠ (n^3 + (n+1)^3) := by 
  intro h
  have eq1 : (n + 2) ^ 3 = n ^ 3 + (n + 1) ^ 3 := by 
    omega -- convert h to the actual equation
  have eq2 : n ≤ 6 := by 
    by_contra h2 
    push_neg at h2 
    have h2' : n ≥ 7 := by omega
    have eq3 : (n + 2 : ℕ) ^ 3 < n ^ 3 + (n + 1) ^ 3 := by 
      have h3 : n ≥ 7 := by linarith 
      have h4 : (n + 2 : ℕ) ^ 3 < n ^ 3 + (n + 1 : ℕ) ^ 3 := by 
        nlinarith [sq_nonneg ((n : ℕ) + 2), sq_nonneg ((n : ℕ) - 1 : ℤ), 
          sq_nonneg ((n : ℕ) - 3 : ℤ), sq_nonneg ((n : ℕ) - 7 : ℤ), 
            sq_nonneg ((n : ℕ) + 1 : ℤ)
          ]
      linarith 
    omega 
  interval_cases n <;> omega