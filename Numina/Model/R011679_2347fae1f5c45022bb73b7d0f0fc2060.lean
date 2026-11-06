import Mathlib

open Int

theorem number_theory_286456 (a : ℤ) (h₀ : a % 10 = 4) (h₁ : ¬(4 ∣ a)) :
    960 ∣ a * (a ^ 2 - 1) * (a ^ 2 - 4) := by
  have h2 : a % 2 = 0 := by 
    omega 
  have h3 : a % 4 = 2 := by 
    omega 
  have h5 : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 3 = 0 := by 
    have h7 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega 
    rcases h7 with (h7 | h7 | h7) <;> simp [h7, Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ]
  -- Show divisible by 5
  have h6 : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 5 = 0 := by
    have h7 : a % 5 = 4 := by omega 
    simp [h7, Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ]
  -- Show divisible by 64
  have h7 : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 64 = 0 := by 
    have h8 : a % 4 = 2 := h3 
    have h9 : a % 2 = 0 := h2 
    have h10 : a % 64 = 2 ∨ a % 64 = 6 ∨ a % 64 = 10 ∨ a % 64 = 14 ∨
        a % 64 = 18 ∨ a % 64 = 22 ∨ a % 64 = 26 ∨ a % 64 = 30 ∨
        a % 64 = 34 ∨ a % 64 = 38 ∨ a % 64 = 42 ∨ a % 64 = 46 ∨
        a % 64 = 50 ∨ a % 64 = 54 ∨ a % 64 = 58 ∨ a % 64 = 62 := by
      omega 
    rcases h10 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [h, Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ] 
  omega