import Mathlib

theorem algebra_323678 (n : ℤ) :
    60 ∣ (n + 1)^6 + n^6 + (n - 1)^6 - 3 * n^2 - 2 := by 
  have h1 : (n + 1)^6 + n^6 + (n - 1)^6 - 3 * n^2 - 2 = 3 * (n ^ 6 + 10 * n ^ 4 + 9 * n ^ 2) := by
    ring
  rw [h1] at *
  have h2 : (n ^ 6 + 10 * n ^ 4 + 9 * n ^ 2) % 4 = 0 := by
    have h3 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3) <;> simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h3]
  have h3 : (n ^ 6 + 10 * n ^ 4 + 9 * n ^ 2) % 5 = 0 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h4]
  omega