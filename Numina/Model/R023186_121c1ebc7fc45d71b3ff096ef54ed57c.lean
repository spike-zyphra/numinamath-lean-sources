import Mathlib

open Real

theorem algebra_15236 (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    (x ^ 2 < x) ∧ (x ^ 2 < 2 * x) ∧ (x ^ 2 < sqrt x) ∧ (x ^ 2 < 1 / x) := by
  rcases hx with ⟨hx0, hx1⟩
  have h1 : x ^ 2 < x := by
    nlinarith [mul_pos (show 0 < x by linarith) (show 0 < 1 - x by nlinarith)]
  have h2 : x ^ 2 < 2 * x := by
    nlinarith [mul_pos (show 0 < x by linarith) (show 0 < 1 - x by nlinarith)]
  have h3 : x ^ 2 < sqrt x := by
    have h4 : (x ^ 2) ^ 2 < x := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), pow_pos (show 0 < x by linarith) 3, pow_pos (show 0 < x by linarith) 4, Real.sqrt_pos.mpr (show 0 < x by linarith), Real.sqrt_pos.mpr (show 0 < x by linarith)]
    have h5 : Real.sqrt x ^ 2 = x := by
      rw [Real.sq_sqrt]
      all_goals linarith
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), pow_pos (show 0 < x by linarith) 2, pow_pos (show 0 < x by linarith) 3, Real.sqrt_pos.mpr (show 0 < x by linarith)]
  have h6 : x ^ 2 < 1 / x := by
    have h7 : x ^ 3 < 1 := by
      nlinarith [mul_pos (show 0 < x by linarith) (show 0 < x by linarith), sq_nonneg (x ^ 2 - 1)]
    have h8 : x ^ 2 < 1 / x := by
      have h_pos : 0 < x := by linarith
      have h14 : x ^ 3 = x ^ 2 * x := by ring
      have h9 : x ^ 3 < 1 := by
        nlinarith [mul_pos (show 0 < x by linarith) (show 0 < x by linarith), sq_nonneg (x ^ 2 - 1)]
      have h13 : x ^ 2 * x < (1 : ℝ) := by linarith
      have h11 : x ^ 2 < (1 / x : ℝ) := by
        have h14 : x > 0 := by linarith
        apply (lt_div_iff₀ h14).mpr
        nlinarith [h13]
      nlinarith
    nlinarith
  constructor
  · exact h1
  constructor
  · exact h2
  constructor
  · exact h3
  · exact h6