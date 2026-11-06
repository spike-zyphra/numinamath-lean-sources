import Mathlib

theorem algebra_137336 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (h1 : b 1 = (a 1) ^ 2) (h2 : b 2 = (a 2) ^ 2)
    (h3 : b 3 = (a 3) ^ 2) (h4 : ∀ n, ∑ i in Finset.range n, b i = √2 + 1) :
    a 0 = -√2 ∧ d = 2 * √2 - 2 := by
  rcases ha with ⟨d, h⟩ 
  rcases hb with ⟨r, hr⟩
  have h5 := h4 0
  simp at h5 
  all_goals nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]