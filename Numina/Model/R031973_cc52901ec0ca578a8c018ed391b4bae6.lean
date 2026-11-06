import Mathlib
theorem number_theory_245717 (a b c d: ℤ) (hc : a ^ 5 * b + 3 = c ^ 3) (hd : a * b ^ 5 + 3 = d ^ 3) : False:= by
  have h1 : c^3 % 9 = 0 ∨ c^3 % 9 = 1 ∨ c^3 % 9 = 8 := by
    have h : c % 9 = 0 ∨ c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 3 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 6 ∨ c % 9 = 7 ∨ c % 9 = 8 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h2 : d^3 % 9 = 0 ∨ d^3 % 9 = 1 ∨ d^3 % 9 = 8 := by
    have h : d % 9 = 0 ∨ d % 9 = 1 ∨ d % 9 = 2 ∨ d % 9 = 3 ∨ d % 9 = 4 ∨ d % 9 = 5 ∨ d % 9 = 6 ∨ d % 9 = 7 ∨ d % 9 = 8 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have eq1 : c^3 % 9 = (a ^ 5 * b + 3) % 9 := by
    omega
  have eq2 : d^3 % 9 = (a * b ^ 5 + 3) % 9 := by
    omega
  have h3 : (a ^ 5 * b + 3) % 9 = 0 ∨ (a ^ 5 * b + 3) % 9 = 1 ∨ (a ^ 5 * b + 3) % 9 = 8 := by
    omega
  have h4 : (a * b ^ 5 + 3) % 9 = 0 ∨ (a * b ^ 5 + 3) % 9 = 1 ∨ (a * b ^ 5 + 3) % 9 = 8 := by
    omega
  have h5 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
    omega
  have h6 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by
    omega
  rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;> 
    simp [Int.add_emod, Int.mul_emod, pow_succ, h5, h6] at h3 h4
    <;> omega