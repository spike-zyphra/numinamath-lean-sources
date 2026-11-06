import Mathlib

open Real

theorem algebra_124108 (x : ℕ → ℝ) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 1) = 1 / (∑ i in Finset.Icc 1 n, x i)) :
    ∃ N, ∀ n, N ≤ n → ∑ i in Finset.Icc 1 n, x i > 1989 := by
  -- Take n = 0 in hxn
  have h1 := hxn 0
  -- This gives x 1 = 1 / (∑ i in Finset.Icc 1 0, x i)
  norm_num [Finset.sum_eq_zero] at h1
  -- sum i in Finset.Icc 1 0, x i is zero (empty sum) 
  -- But this implies x 1 = 1 / 0 which is invalid in Lean 4
  -- Lean 4 automatically rewrite `1 / 0` as `0` in reals
  -- Therefore, Lean 4 now has `x 1 = 0` from h1
  -- But `hx1 : x 1 = 1`
  -- Contradiction: x 1 is supposed to be both 1 and 0
  rw [h1] at hx1
  norm_num at hx1