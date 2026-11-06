import Mathlib

theorem algebra_282068 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n, a n * a (n + 1) * a (n + 2) = a n + a (n + 1) + a (n - 2))
    (hne : ∀ n, a (n + 1) * a (n + 2) ≠ 1) :
    ∑ i in Finset.Icc 1 2004, a i = 4008 := by 
  have h0 := han 0
  simp [ha1, ha2] at h0 
  all_goals omega