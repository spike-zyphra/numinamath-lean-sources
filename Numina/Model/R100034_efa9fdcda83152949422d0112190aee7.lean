import Mathlib

theorem number_theory_253760 (a b c d e f : ℕ) (h₀ : a + b = c + d) (h₁ : b + c = d + e)
    (h₂ : c + d = e + f) (h₃ : a = 28) (h₄ : b = 40) (h₅ : c = 49)
    (h₆ : d.Prime) (h₇ : e.Prime) (h₈ : f.Prime) :
    (d + e + f) / 3 = 12 := by
  subst a b c
  have hd : d = 19 := by
    omega
  have he : e = 70 := by
    omega
  have h9 : ¬ e.Prime := by
    rw [he]
    norm_num [Nat.Prime]
  contradiction