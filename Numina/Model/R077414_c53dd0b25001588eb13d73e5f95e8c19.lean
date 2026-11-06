import Mathlib

theorem number_theory_258494 (n : ℤ) : 6 ∣ n * (2 * n + 1) * (7 * n + 1) := by
  have h1 : n * (2 * n + 1) * (7 * n + 1) % 2 = 0 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega
    rcases h1 with h1 | h1
    · -- If n is even
      simp [h1, Int.mul_emod, Int.add_emod, Int.mul_emod]
    · -- If n is odd, then 7n + 1 is even
      have h2 : 7 * n % 2 = 1 := by
        simp [Int.mul_emod, h1]
      simp [h2, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.add_emod, h1]

  have h2 : n * (2 * n + 1) * (7 * n + 1) % 3 = 0 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h3 with h3 | h3 | h3
    · -- If n ≡ 0 (mod 3)
      simp [h3, Int.mul_emod, Int.add_emod, Int.mul_emod]
    · -- If n ≡ 1 (mod 3)
      simp [h3, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.add_emod]
    · -- If n ≡ 2 (mod 3)
      simp [h3, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.add_emod]
  
  omega