import Mathlib

theorem algebra_232027 (a b c d e : ℕ) (h₀ : a + b = 39) (h₁ : b + c = 40)
    (h₂ : c + d = 38) (h₃ : d + e = 44) (h₄ : a + b + c + d + e = 105) :
    min (min (min (min a b) c) d) e = d := by
  have he : e = 28 := by
    omega
  have hd : d = 16 := by
    rw [show e = 28 by omega] at h₃
    omega
  have hc : c = 22 := by
    rw [show d = 16 by omega] at h₂
    omega
  have hb : b = 18 := by
    rw [show c = 22 by omega] at h₁
    omega
  have ha : a = 21 := by
    rw [show b = 18 by omega] at h₀
    omega
  rw [show a = 21 by omega, show b = 18 by omega, show c = 22 by omega, show d = 16 by omega, show e = 28 by omega]
  all_goals norm_num