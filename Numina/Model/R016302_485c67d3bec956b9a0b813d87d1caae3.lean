import Mathlib

theorem number_theory_195941 (a b c d e f g h i j k l : ℕ)
    (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : d < 10)
    (h₄ : e < 10) (h₅ : f < 10) (h₆ : g < 10) (h₇ : h < 10)
    (h₈ : i < 10) (h₉ : j < 10) (h₁₀ : k < 10) (h₁₁ : l < 10)
    (h₁₂ : a = b) (h₁₃ : b = c) (h₁₄ : d = e) (h₁₅ : e = f)
    (h₁₆ : g = h) (h₁₇ : h = i) (h₁₈ : j = k) (h₁₉ : k = l)
    (h₂₀ : a ≠ 0) (h₂₁ : d ≠ 0) (h₂₂ : g ≠ 0) (h₂₃ : j ≠ 0)
    (h₂₄ : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p^q = 1000 * a + 100 * b + 10 * c + d)
    (h₂₅ : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * q = 1000 * e + 100 * f + 10 * g + h)
    (h₂₆ : ∃ m : ℕ, m^2 = 1000 * i + 100 * j + 10 * k + l) (h₂₇ : 37 ∣ 1000 * l + 100 * k + 10 * j + i) :
    a = 2 ∧ b = 1 ∧ c = 8 ∧ d = 7 := by

  have h28 : i = g := by 
    omega

  have h29 : l = j := by 
    omega

  have h30 : k = j := by 
    omega

  have h31 : j = k := by 
    omega

  have h32 : 37 ∣ 1110 * j + g := by 
    have h33 : 1000 * l + 100 * k + 10 * j + i = 1110 * j + g := by 
      rw [show l = j by omega, show k = j by omega, show i = g by omega]
      all_goals 
        omega 
    rw [h33] at h₂₇ 
    exact h₂₇

  have h34 : j < 10 := by 
    omega

  have h35 : g < 10 := by 
    omega

  have h36 : g ≠ 0 := by 
    omega

  interval_cases j <;> interval_cases g <;> norm_num at h32 <;> omega