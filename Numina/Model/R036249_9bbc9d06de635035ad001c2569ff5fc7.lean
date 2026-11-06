import Mathlib

open Polynomial

theorem algebra_125275 {a : ℕ} (ha : a > 0) (h : (X^2 - X + C (a : ℤ) : Polynomial ℤ) ∣ (X^13 + X + 90 : Polynomial ℤ)) : a = 2 := by 
  rcases h with ⟨q, hq⟩
  have h₁ : ∀ (x : ℤ), (X^2 - X + C (a : ℤ) : Polynomial ℤ).eval x * q.eval x = (X^13 + X + 90).eval x := by 
    intro x
    simp [hq, mul_comm]
  have h₂ := h₁ 0
  simp at h₂
  have h₃ := h₁ (-1)
  simp at h₃
  have h₄ := h₁ 1
  simp at h₄
  have h₅ := h₁ 2
  simp at h₅
  have h₆ := h₁ (-2)
  simp at h₆
  have h16 : a ∣ 90 := by
    have eq1 := h₂
    have h17 : (a : ℤ) ∣ 90 := by 
      use q.eval 0
      all_goals linarith 
    exact Int.ofNat_dvd.mp h17
  have h17 : ((2 + (a : ℤ)) ) ∣ 88 := by
    have eq1 := h₃
    use q.eval (-1)
    all_goals linarith 
  have h18 : a ≤ 90 := by 
    exact Nat.le_of_dvd (by norm_num) h16
  interval_cases a <;> norm_num at h16 h17 h₂ h₃ h₄ h₅ h₆ ⊢
  <;> omega