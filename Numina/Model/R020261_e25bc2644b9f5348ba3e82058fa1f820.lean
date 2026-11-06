import Mathlib

theorem number_theory_242816 (n : ℕ) (a b c : ℕ)
    (h₀ : n % 3 = a) (h₁ : n % 6 = b) (h₂ : n % 9 = c)
    (h₃ : a + b + c = 15) :
    n % 18 = 17 := by
  have ha1 : a ≤ 2 := by
    omega
  have hb1 : b ≤ 5 := by
    omega
  have hc1 : c ≤ 8 := by
    omega
  have ha2 : a = 2 := by
    omega
  have hb2 : b = 5 := by
    omega
  have hc2 : c = 8 := by
    omega
  have h4 : n % 3 = 2 := by
    rw [ha2] at h₀
    omega
  have h5 : n % 6 = 5 := by
    rw [hb2] at h₁
    omega
  have h6 : n % 9 = 8 := by
    rw [hc2] at h₂
    omega
  have h7 : n % 18 = 17 := by
    omega
  exact h7