import Mathlib

/-Egor borrowed 28 rubles from Nikita, and then returned them in four payments. It turned out that Egor always returned a whole number of rubles, and the amount of each payment increased and was divisible by the previous one. What was the last amount Egor paid?-/
theorem number_theory_245162 (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a < b ∧ b < c ∧ c < d) (h₂ : a ∣ b ∧ b ∣ c ∧ c ∣ d)
    (h₃ : a + b + c + d = 28) :
    d = 18 := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  rcases h₁ with ⟨h1, h2, h3⟩
  rcases h₂ with ⟨h4, h5, h6⟩

  have h7: a ≤ 6 := by nlinarith
  have h8 : b ≤ 8 := by nlinarith
  have h9 : c ≤ 12 := by nlinarith

  interval_cases a <;>
  interval_cases b <;>
  interval_cases c <;>
  omega