import Mathlib

theorem algebra_226451 {n : ℤ} : ∃ m, Even m ∧ Even (m + 2) ∧ n * (n + 1) * (n + 2) * (n + 3) = m * (m + 2) := by
  use n ^ 2 + 3 * n
  constructor
  · -- Prove that m is even.
    have h1 : (n ^ 2 + 3 * n : ℤ) % 2 = 0 := by
      have h11 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h11 with (h | h)
      · 
        simp [h, pow_two, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_two, Int.add_emod, Int.mul_emod]
    exact ⟨(n ^ 2 + 3 * n) / 2, by 
      omega 
    ⟩
  constructor
  · -- Prove that m + 2 is even.
    have h2 : (n ^ 2 + 3 * n + 2 : ℤ) % 2 = 0 := by
      have h11 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h11 with (h | h)
      · 
        simp [h, pow_two, Int.add_emod, Int.mul_emod]
      · 
        simp [h, pow_two, Int.add_emod, Int.mul_emod]
    exact ⟨(n ^ 2 + 3 * n + 2) / 2, by 
      omega 
    ⟩
  · -- Prove the functional equation.
    nlinarith [sq_nonneg (n ^ 2 + 3 * n), sq_nonneg (n + 1), sq_nonneg (n + 2)]