import Mathlib

theorem algebra_255225 (a b : ℝ) (m n p : ℝ)
    (h₀ : m ≠ n) (h₁ : m ≠ p) (h₂ : n ≠ p)
    (h₃ : m^3 + a * m + b = 0) (h₄ : n^3 + a * n + b = 0)
    (h₅ : p^3 + a * p + b = 0) :
    m + n + p = 0 := by

  have eq1 : (m - n) * (m^2 + m * n + n^2 + a) = 0 := by 
    have eq1 : m^3 + a * m + b - (n^3 + a * n + b) = 0 := by linarith
    ring_nf at eq1 ⊢
    linarith

  have eq2 : m^2 + m * n + n^2 + a = 0 := by 
    apply (mul_left_inj' (show m - n ≠ 0 by 
      intro h
      apply h₀
      linarith
    )).mp
    linarith
  have eq3 : (m - p) * (m^2 + m * p + p^2 + a) = 0 := by 
    have eq3 : m^3 + a * m + b - (p^3 + a * p + b) = 0 := by linarith
    ring_nf at eq3 ⊢
    linarith

  have eq4 : m^2 + m * p + p^2 + a = 0 := by
    apply (mul_left_inj' (show m - p ≠ 0 by 
      intro h
      apply h₁
      linarith
    )).mp
    linarith

  have eq5 : (n - p) * (n + p + m) = 0 := by
    have eq5 : (m^2 + m * n + n^2 + a) - (m^2 + m * p + p^2 + a) = 0 := by linarith [eq2, eq4]
    ring_nf at eq5 ⊢
    linarith

  cases' (mul_eq_zero.mp eq5) with eq6 eq7
  · -- n - p = 0
    exfalso
    apply h₂
    linarith
  · -- n + p + m = 0
    linarith