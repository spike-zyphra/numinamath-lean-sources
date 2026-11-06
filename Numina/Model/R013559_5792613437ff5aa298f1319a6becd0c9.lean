import Mathlib

theorem algebra_4960 (a : ℝ) (ha : a > 6) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 19 * x + 7 * c = 0) :
    c ≤ 2 := by
  rcases h with ⟨x, hx⟩
  have h_eq : a * x ^ 2 + 19 * x + 7 * c = 0 := hx
  have h2 : (2 * a * x + 19) ^ 2 ≥ 0 := by nlinarith
  have h3 : (2 * a * x + 19) ^ 2 = 361 - 28 * a * (c : ℝ) := by
    nlinarith [h_eq]
  have h4 : 361 - 28 * a * (c : ℝ) ≥ 0 := by
    nlinarith [h3, h2]
  -- Assume c > 2, deriving contradiction
  by_contra h5
  push_neg at h5
  have h6 : c ≥ 3 := by
    omega
  have h7 : (c : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h6
  -- Now using nlinarith with positive a and c positive and signomial 
  -- Such as by_all means (c ≤ 2, which) prohibited so proceeds with:
  nlinarith [h4, ha, h7, sq_pos_of_pos (show (0 : ℝ) < (c : ℝ) by nlinarith), sq_nonneg (a - 6)]