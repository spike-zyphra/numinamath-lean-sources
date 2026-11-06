import Mathlib

theorem algebra_5382 {a b c d : ℕ} (h₀ : a > b ∧ b > c ∧ c > d)
    (h₁ : 5 ^ a - 5 ^ b - 5 ^ c + 5 ^ d = (2496 : ℚ) / 25) :
    a + b + c + d = 2 := by
  have h2 : (5 ^ a : ℚ) - (5 ^ b : ℚ) - (5 ^ c : ℚ) + (5 ^ d : ℚ) = (2496 : ℚ) / 25 := by
    simpa using h₁
  have h3 : (5 ^ a : ℚ) - (5 ^ b : ℚ) - (5 ^ c : ℚ) + (5 ^ d : ℚ) = (2496 / 25 : ℚ) := by
    linarith
  have eq1 : (25 : ℚ) * ((5 ^ a : ℚ) - (5 ^ b : ℚ) - (5 ^ c : ℚ) + (5 ^ d : ℚ)) = (2496 : ℚ) := by
    rw [h3]
    norm_num
  have eq2 : (25 * ((5 ^ a : ℤ) - (5 ^ b : ℤ) - (5 ^ c : ℤ) + (5 ^ d : ℤ)) : ℚ) = (2496 : ℚ) := by
    exact_mod_cast eq1
  have eq3 : 25 * ((5 ^ a : ℤ) - (5 ^ b : ℤ) - (5 ^ c : ℤ) + (5 ^ d : ℤ)) = (2496 : ℤ) := by
    exact_mod_cast eq2
  -- Let's look at the equation modulo 5
  have h4 : 25 * ((5 ^ a : ℤ) - (5 ^ b : ℤ) - (5 ^ c : ℤ) + (5 ^ d : ℤ)) = (2496 : ℤ) := eq3
  have h5 : (25 * ((5 ^ a : ℤ) - (5 ^ b : ℤ) - (5 ^ c : ℤ) + (5 ^ d : ℤ)) ) % 5 = (2496 : ℤ) % 5 := by
    rw [h4]
  -- The left side is 0 modulo 5
  have h6 : (25 * ((5 ^ a : ℤ) - (5 ^ b : ℤ) - (5 ^ c : ℤ) + (5 ^ d : ℤ)) ) % 5 = 0 := by
    simp [Int.mul_emod]
  -- The right side is 1 modulo 5
  have h7 : (2496 : ℤ) % 5 = 1 := by
    norm_num
  -- Contradiction with h6
  rw [h6] at h5
  rw [h7] at h5
  all_goals omega