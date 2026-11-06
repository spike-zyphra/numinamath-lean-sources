import Mathlib

theorem algebra_159084 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = ∑ i in Finset.range n, √(∑ j in Finset.range i, a j))
    (hd : ∃ d, ∀ n, a (n + 1) = a n + d ∧ √(∑ j in Finset.range (n + 1), a j) = √(∑ j in Finset.range n, a j) + d) :
    ∀ n, ∑ i in Finset.range n, a i = n ^ 2 / 4 := by
  rcases hd with ⟨d, hd⟩
  have h1 := hsum 1
  have h0 := hsum 0
  simp [Finset.sum_range_succ] at h1 h0
  have h2 : √(0 : ℝ) = 0 := Real.sqrt_zero
  have h1' : a 0 = 0 := by
    nlinarith [Real.sqrt_nonneg (0 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≥ 0 by norm_num), h2]
  have h11 : 0 < a 0 := ha 0
  linarith [h11, h1']