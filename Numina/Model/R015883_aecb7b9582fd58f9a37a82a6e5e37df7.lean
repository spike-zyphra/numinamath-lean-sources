import Mathlib

theorem algebra_5196 (a c : ℤ) (ha : a > 5) (hroots : ∃ x : ℝ, a * x ^ 2 + 11 * x + 4 * c = 0) :
    c ≤ 1 := by 
  rcases hroots with ⟨x, hx⟩
  have h1 : (a : ℝ) > (5 : ℝ) := by 
    exact_mod_cast ha
  have h2 : (11 : ℝ) ^ 2 - 4 * (a : ℝ) * (4 * (c : ℝ)) ≥ 0 := by
    have h : (a : ℝ) * x ^ 2 + 11 * x + 4 * (c : ℝ) = 0 := by 
      simpa using hx
    nlinarith [sq_nonneg ((a : ℝ) * x + 11 / 2), sq_nonneg (x + (11 : ℝ) / (2 * (a : ℝ))), sq_nonneg (x * (a : ℝ) + 11 / 2), sq_nonneg ((a : ℝ)), sq_pos_of_pos (show (0 : ℝ) < (a : ℝ) - 5 by linarith), sq_nonneg (x)]
  have h3 : (11 : ℤ) ^ 2 - 4 * a * (4 * c) ≥ 0 := by
    have h4 : (11 : ℝ) ^ 2 - 4 * (a : ℝ) * (4 * (c : ℝ)) ≥ 0 := h2
    have h5 : ( (11 : ℤ) ^ 2 - 4 * (a : ℤ) * (4 * (c : ℤ)) ) ≥ (0 : ℤ) := by 
      have h6 : ( (11 : ℤ) ^ 2 - 4 * (a : ℤ) * (4 * (c : ℤ)) ) = ( (11 : ℝ) ^ 2 - 4 * (a : ℝ) * (4 * (c : ℝ)) ) := by
        norm_num
        <;> ring
      rw [h6] at *
      exact_mod_cast h4
    linarith
  have h4 : a ≥ 6 := by 
    omega
  by_contra h
  push_neg at h
  nlinarith [h3, h4, show a * c ≥ 0 from by nlinarith]