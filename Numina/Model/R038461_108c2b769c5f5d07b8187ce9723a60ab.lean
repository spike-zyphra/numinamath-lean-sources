import Mathlib
open Real Set
open scoped BigOperators

theorem algebra_9427 {a : ℝ}:
    (∃ x, logb 3 (a - 3 ^ x) + x - 2 = 0 ∧ 0 < a - 3 ^ x) ↔ a ≥ 6 := by
  constructor
  · -- Assume there exists x such that f(x) = 0 and 0 < a - 3^x, prove a ≥ 6.
    intro h
    rcases h with ⟨x, h_eq, h_pos⟩
    have h1 : logb 3 (a - 3 ^ x) = 2 - x := by linarith
    have h2 : a - 3 ^ x = (3 : ℝ) ^ (2 - x : ℝ) := by
      rw [logb_eq_iff_rpow_eq] at h1
      · nlinarith
      all_goals
        have h3 : (3 : ℝ) ^ (x : ℝ) > 0 := by positivity
        have h4 : a - 3 ^ x > 0 := by linarith
        all_goals
          try linarith
          try positivity
    have h3 : (3 : ℝ) ^ (2 - x : ℝ) = 9 / ((3 : ℝ) ^ (x : ℝ)) := by
      have h31 : (3 : ℝ) ^ (2 - x : ℝ) = (3 : ℝ) ^ (2 : ℝ) / (3 : ℝ) ^ (x : ℝ) := by
        rw [← Real.rpow_sub]
        ring
        all_goals linarith
      have h32 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num
      rw [h31, h32]
      <;> field_simp
    rw [h3] at h2
    have h4 : (3 : ℝ) ^ (x : ℝ) > 0 := by positivity
    have h5 : (a - 3 ^ x) * ((3 : ℝ) ^ (x : ℝ)) = 9 := by
      field_simp [(show (3 : ℝ) ^ (x : ℝ) ≠ 0 by positivity)] at h2 ⊢
      nlinarith
    have h7 : ((3 : ℝ) ^ (x : ℝ)) ^ 2 - a * ((3 : ℝ) ^ (x : ℝ)) + 9 = 0 := by
      nlinarith
    have h8 : a ^ 2 - 36 ≥ 0 := by
      nlinarith [sq_nonneg (((3 : ℝ) ^ (x : ℝ)) - 3), sq_nonneg (a - 6)]
    nlinarith [show a - 6 ≥ 0 from by nlinarith [sq_nonneg (a - 6), sq_nonneg (((3 : ℝ) ^ (x : ℝ)) ^ 2 - 9)]]
  · -- Assume a ≥ 6, prove the existence of x.
    intro ha
    have h10 : a ^ 2 - 36 ≥ 0 := by nlinarith
    have h11 : ∃ y > 0, y ^ 2 - a * y + 9 = 0 := by
      use (a - Real.sqrt (a ^ 2 - 36)) / 2
      constructor
      · -- Show that y > 0.
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 36), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 36 by nlinarith)]
      · -- Show that y^2 - a * y + 9 = 0
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 36), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 36 by nlinarith)]
    rcases h11 with ⟨y, hy_pos, hy_eq⟩
    use Real.logb 3 y
    constructor
    · -- Show that logb 3 (a - 3 ^ x) + x - 2 = 0
      have h30 : (3 : ℝ) ^ (Real.logb 3 y : ℝ) = y := by
        rw [Real.rpow_logb]
        all_goals
          try linarith
      have h40 : a - y = 9 / y := by
        field_simp [(show y ≠ 0 by linarith)]
        nlinarith
      have h100 : logb 3 (a - (3 : ℝ) ^ (Real.logb 3 y : ℝ)) = 2 - Real.logb 3 y := by
        rw [show (3 : ℝ) ^ (Real.logb 3 y : ℝ) = y by linarith [h30]]
        rw [show a - y = 9 / y by linarith [h40]]
        have h50 : (9 / y : ℝ) > 0 := by
          apply div_pos
          all_goals nlinarith
        have h60 : logb 3 (9 / y) = logb 3 9 - logb 3 y := by
          rw [logb_div (by positivity) (by positivity)]
        have h70 : logb 3 9 = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> (norm_num)
        rw [h60, h70]
      nlinarith [h100, Real.logb_pos (show (3 : ℝ) > 1 by linarith) (show (3 : ℝ) > 1 by linarith)]
    · -- Show that 0 < a - 3 ^ x
      have h30 : (3 : ℝ) ^ (Real.logb 3 y : ℝ) = y := by
        rw [Real.rpow_logb]
        all_goals
          try linarith
      have h40 : a - y = 9 / y := by
        field_simp [(show y ≠ 0 by linarith)]
        nlinarith
      rw [show (3 : ℝ) ^ (Real.logb 3 y : ℝ) = y by linarith [h30]]
      have h200 : a - y > 0 := by
        have h400 : (9 / y : ℝ) > 0 := by
          apply div_pos
          all_goals nlinarith
        have h500 : a - y = 9 / y := by linarith [h40]
        nlinarith
      linarith