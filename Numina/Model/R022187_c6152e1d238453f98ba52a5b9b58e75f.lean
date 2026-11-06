import Mathlib

theorem algebra_5854 (a : ℝ) (ha : a > 4) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 11 * x + 3 * c = 0) :
    c ≤ 2 := by
  rcases h with ⟨x, hx⟩
  have h2 : (11 : ℝ) ^ 2 - 4 * a * (3 * (c : ℝ)) ≥ 0 := by
    nlinarith [sq_nonneg (a * x + 11 / 2), sq_nonneg (x + 11 / (2 * a)), sq_nonneg (2 * a * x + 11),
      sq_pos_of_pos (show a - 4 > 0 by linarith)
    ]
  have h3 : (11 : ℝ) ^ 2 ≥ 12 * a * (c : ℝ) := by
    nlinarith [h2]
  have h4 : (121 : ℝ) ≥ 12 * a * (c : ℝ) := by
    nlinarith [h3]
  by_contra h5
  push_neg at h5
  have h6 : c ≥ 3 := by 
    omega
  have h7 : (c : ℝ) ≥ (3 : ℝ) := by
    exact_mod_cast h6
  nlinarith [h4, h7, show a > (4 : ℝ) by linarith]