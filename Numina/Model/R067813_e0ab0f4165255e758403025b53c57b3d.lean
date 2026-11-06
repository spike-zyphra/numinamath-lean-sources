import Mathlib

open Real

theorem algebra_212416 {f : ℕ → ℕ → ℕ}
    (hf1 : f 1 1 = 1)
    (hfm : ∀ m n, f (m + 1) n = f m n + 2 * (m + n))
    (hfn : ∀ m n, f m (n + 1) = f m n + 2 * (m + n - 1)) :
    (∀ m n, f m n = 2 ^ (m - 1) * n) ∧
    (∀ n, ∑ i in Finset.range n, (sqrt (f i i) / 2 ^ (i - 1)) < 6) := by
  have h1 := hfm 0 1
  norm_num at h1
  all_goals omega