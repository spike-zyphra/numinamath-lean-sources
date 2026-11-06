import Mathlib

theorem number_theory_149525 (x : ℕ → ℤ) (h : ∀ n, x (n + 1) = ∑ i in Finset.Icc 1 n, x i ^ 2)
    (hx : x 1 > 0) (h2006 : 2006 ∣ x 2006) :
    x 1 ≥ 118 := by
  have h1 := h 0
  norm_num [Finset.sum_eq_zero] at h1
  all_goals omega