import Mathlib

theorem number_theory_322785 (a b c d m : ℤ) (h₀ : 5 ∣ a * m^3 + b * m^2 + c * m + d)
    (h₁ : ¬5 ∣ d) : ∃ n : ℤ, 5 ∣ d * n^3 + c * n^2 + b * n + a := by
  by_cases h2 : m % 5 = 0
  · -- Case m ≡ 0 (mod 5).
    have h3 : m % 5 = 0 := h2
    have h4 : 5 ∣ d := by
      have h5 : m % 5 = 0 := h3
      have h6 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
        omega
      have h7 : m % 5 = 0 := h5
      simp [pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, h7] at h6
      omega
    omega
  · -- Case m not ≡ 0 (mod 5).
    have h2' : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
      omega
    rcases h2' with (h2 | h2 | h2 | h2)
    · -- Case m % 5 = 1.
      use 1
      have h8 : m % 5 = 1 := h2
      have h6 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
        omega
      have h9 : m % 5 = 1 := h8
      simp [pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, h9] at h6 ⊢
      omega
    · -- Case m % 5 = 2.
      use 3
      have h8 : m % 5 = 2 := h2
      have h6 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
        omega
      have h9 : m % 5 = 2 := h8
      simp [pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, h9] at h6 ⊢
      omega
    · -- Case m % 5 = 3.
      use 2
      have h8 : m % 5 = 3 := h2
      have h6 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
        omega
      have h9 : m % 5 = 3 := h8
      simp [pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, h9] at h6 ⊢
      omega
    · -- Case m % 5 = 4.
      use 4
      have h8 : m % 5 = 4 := h2
      have h6 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
        omega
      have h9 : m % 5 = 4 := h8
      simp [pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, h9] at h6 ⊢
      omega