import Mathlib

theorem number_theory_8053 (n : ℕ) (h₀ : n > 0) :
    ¬ ∃ m, m^2 = n * (n + 1) * (n + 2) * (n + 3) := by 
  rintro ⟨m, hm⟩
  have eq1 : n * (n + 1) * (n + 2) * (n + 3) = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
    ring
  have eq2 : (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) + 1 = (n ^ 2 + 3 * n + 1) ^ 2 := by 
    ring_nf 
  -- Show m^2 < (n ^ 2 + 3 * n + 1) ^ 2
  have eq3 : m ^ 2 < (n ^ 2 + 3 * n + 1) ^ 2 := by 
    have h1 : m ^ 2 = n * (n + 1) * (n + 2) * (n + 3) := by linarith [hm]
    have h2 : n * (n + 1) * (n + 2) * (n + 3) = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
      linarith [eq1]
    have h3 : m ^ 2 = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
      linarith [h1, h2]
    have h4 : (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) < (n ^ 2 + 3 * n + 1) ^ 2 := by
      nlinarith [sq_nonneg (n ^ 2 + 3 * n + 1 : ℕ), sq_nonneg (n : ℕ), sq_pos_of_pos h₀]
    nlinarith [h3, h4]
  have eq4 : m < n ^ 2 + 3 * n + 1 := by
    nlinarith [eq3, sq_nonneg (m : ℕ)]
  have eq7 : (n ^ 2 + 3 * n + 1 : ℕ) ^ 2 = m ^ 2 + 1 := by 
    have h1' : m ^ 2 = n * (n + 1) * (n + 2) * (n + 3) := by linarith [hm]
    have h2' : n * (n + 1) * (n + 2) * (n + 3) = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
      linarith [eq1]
    have eq8 : (n ^ 2 + 3 * n + 1) ^ 2 = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) + 1 := by 
      linarith [eq2]
    have eq9 : m ^ 2 = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
      linarith [h1', h2']
    linarith [eq8, eq9]
  have h10 : (n ^ 2 + 3 * n + 1 : ℕ) = (m + 1) := by 
    by_cases h11 : (n ^ 2 + 3 * n + 1) > (m + 1)
    · -- Assume h11: n^2 + 3 * n + 1 > m + 1
      have h12 : (n ^ 2 + 3 * n + 1) ≥ (m + 2) := by 
        omega 
      nlinarith [sq_nonneg ((n ^ 2 + 3 * n + 1 : ℕ) : ℕ), sq_nonneg ((m : ℕ) : ℕ)]
    · -- Assume not: n^2 + 3 * n + 1 ≤ m + 1
      have h13 : (n ^ 2 + 3 * n + 1 : ℕ) ≤ (m + 1) := by 
        omega 
      have h14 : (n ^ 2 + 3 * n + 1 : ℕ) = (m + 1) := by 
        nlinarith [sq_nonneg ((n ^ 2 + 3 * n + 1 : ℕ) : ℕ), sq_nonneg ((m : ℕ) : ℕ)]
      linarith [h14]
  have h11 : m = (n ^ 2 + 3 * n) := by 
    omega 
  have h12 : (n ^ 2 + 3 * n) ^ 2 = n * (n + 1) * (n + 2) * (n + 3) := by
    rw [h11] at hm 
    linarith 
  nlinarith [sq_nonneg (n : ℕ), sq_pos_of_pos h₀, h₀]