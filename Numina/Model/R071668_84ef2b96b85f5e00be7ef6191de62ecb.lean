import Mathlib

theorem number_theory_23020 (a b c d : ℤ) (h₀ : ¬(a ≡ b [ZMOD 6])) (h₁ : ¬(a ≡ c [ZMOD 6]))
    (h₂ : ¬(a ≡ d [ZMOD 6])) (h₃ : ¬(b ≡ c [ZMOD 6])) (h₄ : ¬(b ≡ d [ZMOD 6])) (h₅ : ¬(c ≡ d [ZMOD 6]))
    (h₆ : ¬(6 ∣ a * b * c * d)) :
    (a * b * c * d) % 6 = 4 := by

  have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by 
    omega
  have h2 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by 
    omega
  have h3 : c % 6 = 0 ∨ c % 6 = 1 ∨ c % 6 = 2 ∨ c % 6 = 3 ∨ c % 6 = 4 ∨ c % 6 = 5 := by 
    omega
  have h4 : d % 6 = 0 ∨ d % 6 = 1 ∨ d % 6 = 2 ∨ d % 6 = 3 ∨ d % 6 = 4 ∨ d % 6 = 5 := by 
    omega

  rcases h1 with (hA | hA | hA | hA | hA | hA) <;> rcases h2 with (hB | hB | hB | hB | hB | hB) <;> rcases h3 with (hC | hC | hC | hC | hC | hC) <;> rcases h4 with (hD | hD | hD | hD | hD | hD) <;> 
    ( 
      simp [Int.ModEq, Int.dvd_iff_emod_eq_zero, Int.mul_emod, hA, hB, hC, hD] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ ⊢ 
      <;> omega
    )