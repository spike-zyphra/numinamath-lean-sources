import Mathlib

theorem number_theory_5867 (a b n : ℤ) (hab : a.gcd b = 1) :
  ∃ x y, n = a * x + b * y := by
  have h1 : ∃ x y, a * x + b * y = 1 := by
    have h2 : a.gcd b = 1 := hab
    have h3 : IsCoprime a b := by 
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact h2
    rcases h3 with ⟨x, y, h4⟩
    exact ⟨x, y, by linarith⟩
  rcases h1 with ⟨x0, y0, h_eq⟩
  use n * x0, n * y0
  have h3 : a * (n * x0) + b * (n * y0) = n := by
    calc 
      a * (n * x0) + b * (n * y0) = n * (a * x0 + b * y0) := by ring
      _ = n * 1 := by 
        rw [h_eq]
      _ = n := by 
        ring
  linarith [h3]