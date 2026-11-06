import Mathlib

theorem number_theory_6114 {a b c d m : ℤ} (h₀ : a ≡ b [ZMOD m]) (h₁ : c ≡ d [ZMOD m]) :
    m ∣ (a - b) ∧ m ∣ (c - d) := by
  constructor
  · -- prove m ∣ (a - b)
    exact Int.dvd_of_emod_eq_zero (by
      have h2 : a % m = b % m := h₀
      have h3 : (a - b) % m = 0 := by
        simp [Int.sub_emod, h2]
      exact h3
    )
  · -- prove m ∣ (c - d)
    exact Int.dvd_of_emod_eq_zero (by
      have h4 : c % m = d % m := h₁
      have h5 : (c - d) % m = 0 := by
        simp [Int.sub_emod, h4]
      exact h5
    )