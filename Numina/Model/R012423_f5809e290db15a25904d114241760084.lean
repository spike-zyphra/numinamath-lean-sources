import Mathlib

theorem algebra_6861 (a : ℝ) (ha : a > 5) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 8 * x - 3 * c = 0) :
    c ≥ -1 := by
  rcases h with ⟨x, hx⟩
  by_contra h2
  push_neg at h2
  have h3 : c ≤ -2 := by omega
  have h4 : (c : ℝ) ≤ -2 := by exact_mod_cast h3
  nlinarith [sq_nonneg (a * x + 4), sq_nonneg (x + 4 / a), sq_nonneg (a - 5), 
          sq_nonneg ((8 : ℝ) + 2 * a * x), sq_nonneg (x + 4 / a), 
          sq_nonneg (a * x + 4), sq_pos_of_pos (show (0 : ℝ) < a by linarith)
        ]