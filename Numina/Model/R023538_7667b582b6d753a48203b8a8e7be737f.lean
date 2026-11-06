import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185619 (f : ℝ → ℝ) (hf : f = λ x => sin (π * x) + sqrt 3 * cos (π * x / 2)) :
    IsGreatest {x | x < 0 ∧ f x = 0} (-2 / 3) := by
  constructor
  · -- Show $-2/3$ is in the set
    constructor
    · -- Show $-2/3 < 0$
      norm_num
    · -- Show $f(-2/3) = 0$
      have h1 : f (-2 / 3) = sin (π * (-2 / 3)) + sqrt 3 * cos (π * (-2 / 3) / 2) := by 
        rw [hf]
      rw [h1]
      have h2 : sin (π * (-2 / 3)) = -sin (2 * π / 3) := by 
        have h3 : π * (-2 / 3) = -(2 * π / 3) := by 
          ring
        rw [h3]
        rw [sin_neg]
      have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by 
        have h5 : 2 * π / 3 = π - (π / 3) := by 
          ring
        rw [h5]
        rw [sin_pi_sub]
        have h6 : sin (π / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
        rw [h6]
      have h7 : cos (π * (-2 / 3) / 2) = 1 / 2 := by 
        have h8 : π * (-2 / 3) / 2 = -(π / 3) := by 
          linarith [Real.pi_pos]
        rw [h8]
        rw [cos_neg]
        have h9 : cos (π / 3) = 1 / 2 := cos_pi_div_three
        rw [h9]
      rw [h2, h4, h7]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
  · -- Show $-2/3$ is greatest in the set
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    by_contra h
    push_neg at h
    have h1 : f x = sin (π * x) + sqrt 3 * cos (π * x / 2) := by 
      rw [hf]
    rw [h1] at hx2
    have h4 : sin (π * x) = 2 * sin (π * x / 2) * cos (π * x / 2) := by
      have h2 : sin (π * x) = 2 * sin (π * x / 2) * cos (π * x / 2) := by
        have h3 : sin (π * x) = sin (2 * (π * x / 2)) := by ring
        rw [h3]
        rw [sin_two_mul]
      linarith
    rw [h4] at hx2
    have h5 : cos (π * x / 2) * (2 * sin (π * x / 2) + sqrt 3) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case h6 : cos (π * x / 2) = 0
      have h8 : cos (π * x / 2) = 0 := by
        linarith
      have h9 : -2 / 3 < x := by linarith
      have h10 : x < 0 := by linarith
      have h11 : π * x / 2 > -(Real.pi / 3 : ℝ) := by 
        nlinarith [pi_pos, Real.pi_pos]
      have h12 : π * x / 2 < 0 := by 
        nlinarith [pi_pos, show x < 0 by linarith]
      have h14 : cos (π * x / 2) > 0 := by 
        apply cos_pos_of_mem_Ioo
        constructor
        · -- Proof that $-(\pi)/2 < \pi x/2$.
          nlinarith [show Real.pi > 0 by exact pi_pos, Real.pi_pos]
        · -- Proof that $\pi x/2 < \pi/2$.
          nlinarith [show Real.pi > 0 by exact pi_pos, Real.pi_pos]
      linarith [h14, h8]
    · -- Case h7 : 2 * sin (π * x / 2) + sqrt 3 = 0
      have h8 : 2 * sin (π * x / 2) + sqrt 3 = 0 := by 
        linarith
      have h9 : -2 / 3 < x := by linarith
      have h10 : x < 0 := by linarith
      have h11 : π * x / 2 > -(Real.pi / 3 : ℝ) := by 
        nlinarith [pi_pos, Real.pi_pos]
      have h12 : π * x / 2 < 0 := by 
        nlinarith [pi_pos, show x < 0 by linarith]
      have h13 : sin (π * x / 2) > -(Real.sqrt 3 / 2 : ℝ) := by
        have h17 : sin (π * x / 2) > -Real.sqrt 3 / 2 := by
          have h18 : π * x / 2 > -(Real.pi / 3) := by 
            nlinarith [pi_pos, Real.pi_pos]
          have h19 : sin (π * x / 2) > sin (-(Real.pi / 3)) := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              nlinarith [pi_pos, show Real.pi > 0 by exact pi_pos]
          have h20 : sin (-(Real.pi / 3 : ℝ)) = - Real.sqrt 3 / 2 := by 
            rw [show sin (-(Real.pi / 3 : ℝ)) = - sin (Real.pi / 3 : ℝ) by rw [sin_neg]]
            have h21 : sin (Real.pi / 3 : ℝ) = Real.sqrt 3 / 2 := by 
              rw [sin_pi_div_three]
            linarith
          nlinarith [show Real.sqrt 3 > 0 by positivity, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
        linarith
      have h14 : sin (π * x / 2) = - Real.sqrt 3 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
      linarith