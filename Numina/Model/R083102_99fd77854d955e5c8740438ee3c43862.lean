import Mathlib

theorem number_theory_182686 (a b : ℤ) (h₀ : 10 ∣ a + b) :
    a^2 ≡ b^2 [ZMOD 10] := by 
  have h₁ : b ≡ -a [ZMOD 10] := by
    have h₂ : a + b ≡ 0 [ZMOD 10] := by 
      exact Int.dvd_iff_emod_eq_zero.mp h₀
    have h₃ : b ≡ -a [ZMOD 10] := by 
      simp [Int.ModEq] at h₂ ⊢
      omega
    exact h₃
  have h₂ : (a)^2 ≡ (b)^2 [ZMOD 10] := by
    -- This derivation is going through congruence.
    have h₄ : a ≡ -b [ZMOD 10] := by 
      simp [Int.ModEq] at h₁ ⊢
      omega
    have h₅ : (a)^2 ≡ (-b)^2 [ZMOD 10] := by
      apply Int.ModEq.pow 
      exact h₄
    have h₆ : (-b : ℤ) ^ 2 = (b : ℤ) ^ 2 := by ring
    rw [h₆] at h₅
    exact h₅
  exact h₂