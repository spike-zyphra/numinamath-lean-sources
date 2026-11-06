import Mathlib

theorem algebra_314215 (f : ℝ → ℝ) (hf : f = fun x => x * abs x - (4 * Real.cos (Real.pi / 6)) * x + 2) :
    {x | f x = 0}.encard = 3 := by
  have h1 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
    rw [Real.cos_pi_div_six]
  have h2 : (4 * Real.cos (Real.pi / 6) : ℝ) = 2 * Real.sqrt 3 := by
    rw [h1]
    ring_nf
  have h3 : {x | f x = 0} = {Real.sqrt 3 + 1, Real.sqrt 3 - 1, -Real.sqrt 3 - Real.sqrt 5} := by
    ext x
    simp [hf, h2]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {√3 + 1, √3 - 1, -√3 - √5}
      intro h_eq
      by_cases h : x ≥ 0
      · -- If x ≥ 0, then |x| = x
        have h4 : abs x = x := abs_of_nonneg h
        rw [h4] at h_eq
        have h5 : x ^ 2 - (2 * Real.sqrt 3) * x + 2 = 0 := by
          linarith
        have h6 : (x - (Real.sqrt 3 + 1)) * (x - (Real.sqrt 3 - 1)) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- First solution
          have h8 : x = Real.sqrt 3 + 1 := by linarith
          rw [h8]
          tauto
        · -- Second solution
          have h9 : x = Real.sqrt 3 - 1 := by linarith
          rw [h9]
          tauto
      · -- Case x < 0
        have h4 : abs x = -x := by
          rw [abs_of_neg (show x < 0 by linarith)]
        rw [h4] at h_eq
        have h7 : -x ^ 2 - (2 * Real.sqrt 3) * x + 2 = 0 := by
          linarith
        have h8 : (x + Real.sqrt 3 + Real.sqrt 5) * (x + Real.sqrt 3 - Real.sqrt 5) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 5 ^ 2 - 5), Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]
        cases' (mul_eq_zero.mp h8) with h9 h10
        · -- First solution
          have h11 : x = -Real.sqrt 3 - Real.sqrt 5 := by linarith
          rw [h11]
          tauto
        · -- Second solution
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 5 ^ 2 - 5), Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]
    · -- Assume x ∈ {√3 + 1, √3 - 1, -√3 - √5}, prove f(x) = 0
      intro h_eq
      rcases h_eq with (rfl | rfl | rfl)
      · -- First positive root
        have h4 : abs (Real.sqrt 3 + 1 : ℝ) = Real.sqrt 3 + 1 := abs_of_nonneg (by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)])
        rw [h4]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      · -- Second positive root
        have h4 : abs (Real.sqrt 3 - 1 : ℝ) = Real.sqrt 3 - 1 := abs_of_nonneg (by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)])
        rw [h4]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      · -- Negative root
        have h4 : abs (-Real.sqrt 3 - Real.sqrt 5 : ℝ) = - (-Real.sqrt 3 - Real.sqrt 5) := by
          rw [abs_of_neg]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
        rw [h4]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]
  rw [h3]
  have h4 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h5 : Real.sqrt 5 > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h6 : Real.sqrt 3 + 1 > 0 := by
    linarith [h4]
  have h7 : Real.sqrt 3 - 1 > 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  have h8 : -Real.sqrt 3 - Real.sqrt 5 < 0 := by
    linarith [show Real.sqrt 3 > 0 by apply Real.sqrt_pos.mpr; linarith, show Real.sqrt 5 > 0 by apply Real.sqrt_pos.mpr; linarith]
  have h9 : Real.sqrt 3 + 1 ≠ Real.sqrt 3 - 1 := by
    linarith [h4]
  have h10 : Real.sqrt 3 + 1 ≠ -Real.sqrt 3 - Real.sqrt 5 := by
    linarith [h4, h5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
  have h11 : Real.sqrt 3 - 1 ≠ -Real.sqrt 3 - Real.sqrt 5 := by
    linarith [h4, h5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton, h9, h10, h11]
  all_goals linarith