import Mathlib
open Nat

theorem number_theory_607174 (a b : ℤ) (h₀ : ¬ 3 ∣ a) (h₁ : ¬ 3 ∣ b) :
    3 ∣ a^4 - b^2 := by

  have h2 : a^4 % 3 = 1 := by
    have : a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    rcases this with (h | h)
    · 
      simp [h, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega

  have h3 : b^2 % 3 = 1 := by
    have : b % 3 = 1 ∨ b % 3 = 2 := by 
      omega 
    rcases this with (h | h)
    · 
      simp [h, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega

  omega