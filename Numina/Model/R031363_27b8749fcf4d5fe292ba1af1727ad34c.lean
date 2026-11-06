import Mathlib

theorem algebra_323768 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n > 0, a (n + 1) * a n + a (n + 1) - 2 * a n = 0) :
    IsLeast {x | ∀ n, ∑ i in Finset.Icc 1 n, a i * (a i - 1) < x} 3 := by

  have h2 := han 1 (by norm_num)
  simp [ha1] at h2
  all_goals omega