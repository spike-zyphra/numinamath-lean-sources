import Mathlib

theorem number_theory_7251 {a b c d n : ℤ} (h₀ : n = a^2 + b^2) (h₁ : n = c^2 + d^2)
    (h₂ : a ≠ c) (h₃ : a ≠ d) (h₄ : b ≠ c) (h₅ : b ≠ d) :
    n = ((a - c)^2 + (b - d)^2) * ((a + c)^2 + (b - d)^2) / (4 * (b - d)^2) := by 
  have h6 : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by linarith
  have h7 : (b - d) ≠ 0 := by
    intro h8
    have h9 : b = d := by linarith
    omega

  have h8 : 4 * (b - d) ^ 2 * n = ((a - c) ^ 2 + (b - d) ^ 2) * ((a + c) ^ 2 + (b - d) ^ 2) := by
    have h16 : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by linarith
    rw [show n = a ^ 2 + b ^ 2 by linarith]
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c), sq_nonneg (b - d), sq_nonneg (a - d), sq_nonneg (b - c)]
  
  have h17 : (4 * (b - d) ^ 2) ≠ 0 := by
    have h7 : (b - d) ≠ 0 := by
      intro h8
      have h9 : b = d := by linarith
      omega
    have h18 : (b - d) ^ 2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h7
    have h19 : 4 * (b - d) ^ 2 ≠ 0 := by
      omega
    assumption

  have h14 : ((a - c) ^ 2 + (b - d) ^ 2) * ((a + c) ^ 2 + (b - d) ^ 2) / (4 * (b - d) ^ 2) = n := by
    have h10 : 4 * (b - d) ^ 2 ∣ ((a - c) ^ 2 + (b - d) ^ 2) * ((a + c) ^ 2 + (b - d) ^ 2) := by
      use n
      linarith [h8]

    have h11 : ((a - c) ^ 2 + (b - d) ^ 2) * ((a + c) ^ 2 + (b - d) ^ 2) = 4 * (b - d) ^ 2 * n := by
      linarith [h8]

    have h14 : ((a - c) ^ 2 + (b - d) ^ 2) * ((a + c) ^ 2 + (b - d) ^ 2) / (4 * (b - d) ^ 2) = n := by
      rw [h11]
      field_simp [h17]
    assumption

  linarith [h14, h₀]