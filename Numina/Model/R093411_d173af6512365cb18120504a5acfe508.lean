import Mathlib

theorem number_theory_105309 (n : ℤ) : Odd (n^2 + n + 1) := by 
  have h : (n ^ 2 + n + 1) % 2 = 1 := by 
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega 
    rcases h1 with (h1 | h1)
    · -- If n % 2 = 0 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    · -- If n % 2 = 1 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
  exact ⟨(n^2 + n + 1) / 2, by omega⟩