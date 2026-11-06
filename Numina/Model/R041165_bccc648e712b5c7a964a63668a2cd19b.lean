import Mathlib


theorem number_theory_232445 (a1 a2 b1 b2 c1 c2 d : ℤ) (h₀ : d ≠ 0) (h₁ : a1 - a2 ≡ 0 [ZMOD d]) (h₂ : b1 - b2 ≡ 0 [ZMOD d]) (h₃ : c1 - c2 ≡ 0 [ZMOD d]) :
    (a1 * b1 * c1 - a2 * b2 * c2) ≡ 0 [ZMOD d] := by 
  norm_num [Int.ModEq] at h₁ h₂ h₃ ⊢
  have h7 : d ∣ a1 * b1 * c1 - a2 * b2 * c2 := by
    have h8 : d ∣ a1 - a2 := by
      exact_mod_cast h₁
    have h9 : d ∣ b1 - b2 := by
      exact_mod_cast h₂
    have h10 : d ∣ c1 - c2 := by
      exact_mod_cast h₃
    -- Express $a1 * b1 * c1 - a2 * b2 * c2$ as a sum of products of the differences
    have h12 : a1 * b1 * c1 - a2 * b2 * c2 = (a1 - a2) * (b1 * c1) + (b1 - b2) * (a2 * c1) + (c1 - c2) * (a2 * b2) := by
      ring
    rw [h12]
    apply dvd_add
    apply dvd_add
    · -- First term is divisible by d
      apply dvd_mul_of_dvd_left
      exact h8
    · -- Second term is divisible by d
      apply dvd_mul_of_dvd_left
      exact h9
    · -- Third term is divisible by d
      apply dvd_mul_of_dvd_left
      exact h10
  exact_mod_cast h7