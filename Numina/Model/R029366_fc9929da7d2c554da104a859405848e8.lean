import Mathlib

theorem algebra_21394 {a b c d : ℤ} (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : a + b = 16) (h₄ : a + c = 19) (h₅ : a + d = 20) (h₆ : b + c = 21)
    (h₇ : b + d = 22) (h₈ : c + d = 25) :
    a = 7 ∧ b = 9 ∧ c = 12 ∧ d = 13 := by
  have hb : b = 16 - a := by
    omega
  have hc : c = 19 - a := by
    omega
  have hd : d = 20 - a := by
    omega
  rw [hb, hc] at h₆
  have ha : a = 7 := by
    omega
  have hb' : b = 9 := by
    rw [ha] at hb
    omega
  have hc' : c = 12 := by
    rw [ha] at hc
    omega
  have hd' : d = 13 := by
    rw [ha] at hd
    omega
  exact ⟨by omega, by omega, by omega, by omega⟩