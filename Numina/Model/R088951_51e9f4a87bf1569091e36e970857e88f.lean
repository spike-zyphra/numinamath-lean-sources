import Mathlib

theorem number_theory_255031 {n : ℤ} (hn : n^3 = (n-1)^3 + (n-2)^3 + (n-3)^3) :
    n = 6 := by
  have eq1 : n^3 = (n-1)^3 + (n-2)^3 + (n-3)^3 := hn
  have h1 : n^3 - ( (n-1)^3 + (n-2)^3 + (n-3)^3 ) = 0 := by
    linarith [eq1]
  have h2 : (n - 6) * (n^2 - 3 * n + 3) = 0 := by 
    ring_nf at h1 ⊢ 
    linarith
  cases (mul_eq_zero.1 h2) with
  | inl h3 =>
    linarith 
  | inr h4 =>
    have h5 : n^2 - 3 * n + 3 > 0 := by 
      nlinarith [sq_nonneg (n - 1), sq_nonneg (n - 2), sq_nonneg (n - 3)]
    have h6 : n^2 - 3 * n + 3 = 0 := h4
    linarith