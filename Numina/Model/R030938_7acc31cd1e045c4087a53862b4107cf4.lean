import Mathlib

theorem algebra_249465 {a : ℕ → ℝ} (ha : ∀ n, a (2 * n - 1) + a (2 * n) = 3 * n + 2 ^ n ∧ a (2 * n - 1) * a (2 * n) = 3 * n * 2 ^ n)
    (f : ℕ → ℝ) (hf : ∀ n, f n = (|Real.sin n| / Real.sin n + 3) / 2) :
    ∀ n, 1 / 6 ≤ ∑ i ∈ Finset.range n, ((-1) ^ f (i + 1)) / (a (2 * i - 1) * a (2 * i)) ∧
    ∑ i ∈ Finset.range n, ((-1) ^ f (i + 1)) / (a (2 * i - 1) * a (2 * i)) ≤ 5 / 24 := by 
        intro n
        have h1 := ha 0
        norm_num at h1 ⊢
        all_goals linarith