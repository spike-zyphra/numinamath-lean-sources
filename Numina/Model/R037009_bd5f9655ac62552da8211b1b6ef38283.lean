import Mathlib

theorem number_theory_63529 (a : ℤ) (ha : 5 ≤ a) :
    ∃ b c : ℤ, c ≥ b ∧ b ≥ a ∧ a^2 + b^2 = c^2 := by
  by_cases h : a % 2 = 1
  · -- Case a is odd
    use (a^2 - 1) / 2
    use (a^2 + 1) / 2
    have h1 : (a ^ 2 + 1 : ℤ) / 2 ≥ (a ^ 2 - 1 : ℤ) / 2 := by
      have h2 : a ^ 2 + 1 ≥ a ^ 2 - 1 := by 
        omega
      omega
    have h2 : (a ^ 2 - 1 : ℤ) / 2 ≥ a := by
      have h3 : a ^ 2 -1 ≥ 2 * a := by
        nlinarith [sq_nonneg (a - 3 : ℤ)]
      have h4 : (a ^ 2 - 1 : ℤ) % 2 = 0 := by 
        have : a % 2 = 1 := h
        have h5 : a ^ 2 % 2 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, this]
        omega
      omega
    have h3 : a^2 + ((a^2 - 1 : ℤ) / 2) ^ 2 = ((a^2 + 1 : ℤ) / 2) ^ 2 := by
      have h4 : (a : ℤ) % 2 = 1 := h
      have h5 : (a ^ 2 : ℤ) % 2 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
      have h6 : (a ^ 2 - 1 : ℤ) % 2 = 0 := by
        omega
      have h7 : (a ^ 2 + 1 : ℤ) % 2 = 0 := by
        omega
      have h8 : (a ^ 2 - 1 : ℤ) / 2 = (a^2 -1) / 2 := by omega
      have h9 : (a ^ 2 + 1 : ℤ) / 2 = (a^2 +1) / 2 := by omega
      rw [h8, h9]
      have eq1 : 2 * ((a^2 -1) / 2) = a^2 - 1 := by
        omega
      have eq2 : 2 * ((a^2 +1) / 2) = a^2 + 1 := by
        omega
      nlinarith [sq_nonneg (a^2 * 0)]
    constructor
    · -- Show c ≥ b 
      omega
    constructor
    · -- Show b ≥ a 
      omega
    · -- Show a^2 + b^2 = c^2
      nlinarith
  · -- Case a is even
    have h2 : a % 2 = 0 := by
      omega
    have h4 : ∃ k : ℤ, a = 2 * k := by 
      refine' ⟨a / 2, by 
        omega
      ⟩
    rcases h4 with ⟨k, hk⟩
    use k^2 - 1
    use k^2 + 1
    have h5 : k ≥ 3 := by
      nlinarith [show a ≥ 6 from by omega, sq_nonneg (a - 6 : ℤ), sq_nonneg (k - 3 : ℤ)]
    constructor
    · -- Show c ≥ b 
      nlinarith [sq_nonneg (k ^ 2 * 0)]
    constructor
    · -- Show b ≥ a 
      rw [show a = 2 * k by linarith]
      nlinarith [sq_nonneg (k * 0)]
    · -- Show a^2 + b^2 = c^2 
      rw [show a = 2 * k by linarith]
      nlinarith [sq_nonneg (k ^ 2 * 0)]