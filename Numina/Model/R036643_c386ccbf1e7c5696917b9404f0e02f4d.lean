import Mathlib

theorem algebra_34676 {n : ℤ} (hn : n > 1) :
    ∃ a b, a^2 - b^2 = n^3 ∧ a > 0 ∧ b > 0 := by
  have h1 : n ≥ 2 := by linarith
  use (n^2 + n)/2, (n^2 - n)/2
  constructor
  · -- Show a^2 - b^2 = n^3
    have h3 : (n^2 + n) % 2 = 0 := by
      have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h3 with (h3 | h3)
      · -- n is even
        simp [h3, Int.add_emod, Int.mul_emod, pow_two]
      · -- n is odd
        simp [h3, Int.add_emod, Int.mul_emod, pow_two]
    have h4 : (n^2 - n) % 2 = 0 := by
      have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h4 with (h4 | h4)
      · -- n is even
        simp [h4, Int.sub_emod, Int.mul_emod, pow_two]
      · -- n is odd
        simp [h4, Int.sub_emod, Int.mul_emod, pow_two]
    have h5 : ( (n^2 + n)/2 : ℤ) ^ 2 - ( (n^2 - n)/2 : ℤ) ^ 2 = n^3 := by
      have h6 : (n^2 + n) % 2 = 0 := h3
      have h7 : (n^2 - n) % 2 = 0 := h4
      have h8 : (n^2 + n)/2 * 2 = n^2 + n := by 
        omega
      have h9 : (n^2 - n)/2 * 2 = n^2 - n := by 
        omega
      have h10 : ( (n^2 + n)/2 : ℤ) - ( (n^2 - n)/2 : ℤ) = n := by 
        have h9' : ( (n^2 + n)/2 : ℤ) - ( (n^2 - n)/2 : ℤ) = n := by
          have h10 : (n^2 + n)/2 - (n^2 - n)/2 = (n^2 + n - (n^2 - n)) / 2 := by 
            omega
          have h11 : n^2 + n - (n^2 - n) = 2 * n := by 
            linarith
          have h12 : (n^2 + n)/2 - (n^2 - n)/2 = (2 * n) / 2 := by 
            rw [h10, h11]
          have h13 : (2 * n) / 2 = n := by 
            omega
          linarith [h12, h13]
        linarith [h9']
      have h11 : ( (n^2 + n)/2 : ℤ) + ( (n^2 - n)/2 : ℤ) = n^2 := by 
        have h9' : ( (n^2 + n)/2 : ℤ) + ( (n^2 - n)/2 : ℤ) = n^2 := by
          have h10 : (n^2 + n)/2 + (n^2 - n)/2 = (n^2 + n + (n^2 - n)) / 2 := by 
            omega
          have h11 : n^2 + n + (n^2 - n) = 2 * n^2 := by 
            linarith
          have h12 : (n^2 + n)/2 + (n^2 - n)/2 = (2 * n^2) / 2 := by 
            rw [h10, h11]
          have h13 : (2 * n^2) / 2 = n^2 := by 
            omega
          linarith [h12, h13]
        linarith [h9']
      calc
        ( (n^2 + n)/2 : ℤ) ^ 2 - ( (n^2 - n)/2 : ℤ) ^ 2
          = ( ( (n^2 + n)/2 : ℤ) - ( (n^2 - n)/2 : ℤ) ) * ( ( (n^2 + n)/2 : ℤ) + ( (n^2 - n)/2 : ℤ) ) := by ring
        _ = n * n^2 := by rw [h10, h11]
        _ = n^3 := by ring
    exact h5

  constructor
  · -- Show a > 0
    have h5 : ( (n^2 + n)/2 : ℤ) > 0 := by
      have h3 : n ≥ 2 := by linarith
      have h4 : n ^ 2 + n ≥ 6 := by
        nlinarith [sq_nonneg (n - 2 : ℤ)]
      have h8' : (n^2 + n) % 2 = 0 := by
        have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h3 with (h3 | h3)
        · -- n is even
          simp [h3, Int.add_emod, Int.mul_emod, pow_two]
        · -- n is odd
          simp [h3, Int.add_emod, Int.mul_emod, pow_two]
      have h6 : ( (n^2 + n)/2 : ℤ) ≥ 3 := by
        omega
      omega
    linarith
  · -- Show b > 0
    have h7 : ( (n^2 - n)/2 : ℤ) > 0 := by
      have h3 : n ≥ 2 := by linarith
      have h8 : n^2 - n ≥ 2 := by
        nlinarith [sq_nonneg (n - 2 : ℤ)]
      have h4' : (n^2 - n) % 2 = 0 := by 
        have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h4 with (h4 | h4)
        · -- n is even
          simp [h4, Int.sub_emod, Int.mul_emod, pow_two]
        · -- n is odd
          simp [h4, Int.sub_emod, Int.mul_emod, pow_two]
      have h6 : ( (n^2 - n)/2 : ℤ) ≥ 1 := by
        omega
      omega
    linarith