import Mathlib
open Complex Filter Function Metric Finset
open scoped BigOperators Topology

/- Let the complex number $z=9+10\text{i}$ (where $\text{i}$ is the imaginary unit). If the positive integer $n$ satisfies $\left|{z}^{n}\right|\leqslant2023$, then the maximum value of $n$ is ___          ___. -/
theorem algebra_8558 {z : ℂ} (hz : z = 9 + 10 * .I) :
    IsGreatest {n | 0 < n ∧ ‖z ^ n‖ ≤ 2023} 2 := by 
  constructor
  · -- Show that 2 is in the set
    constructor
    · norm_num 
    · -- Show that ‖z ^ 2‖ ≤ 2023
      rw [hz]
      simp [Complex.norm_eq_abs, pow_two, Complex.abs, Complex.normSq]
      ring_nf
      norm_num [Real.sqrt_le_iff, Real.sqrt_nonneg]
  · -- Show that 2 is the greatest
    intro n hn
    rcases hn with ⟨hn_pos, hn_norm⟩
    by_contra h
    push_neg at h
    have h3 : n ≥ 3 := by 
      omega
    have hz1 : ‖z‖ = Real.sqrt 181 := by 
      rw [hz]
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      ring_nf
    have h6 : ‖z ^ n‖ = ‖z‖ ^ n := by 
      simp [norm_pow]
    rw [h6, hz1] at hn_norm 
    have h7 : Real.sqrt 181 ^ 3 > 2023 := by 
      have h8 : Real.sqrt 181 ^ 2 = 181 := Real.sq_sqrt (by norm_num)
      have h9 : Real.sqrt 181 ^ 3 = Real.sqrt 181 ^ 2 * Real.sqrt 181 := by 
        ring_nf 
      rw [h9, h8]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 181 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 181 by norm_num)]
    have h8 : Real.sqrt 181 ^ n ≥ Real.sqrt 181 ^ 3 := by 
      have h9 : Real.sqrt 181 > 1 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 181 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 181 by norm_num)]
      have h10 : (3 : ℝ) ≤ (n : ℝ) := by 
        have hn' : n ≥ 3 := h3
        exact_mod_cast hn'
      have h11 : Real.sqrt 181 ^ (3 : ℝ) ≤ Real.sqrt 181 ^ (n : ℝ) := by 
        apply Real.rpow_le_rpow_of_exponent_le 
        · linarith 
        · exact_mod_cast h3 
      have h12 : (Real.sqrt 181 ^ 3 : ℝ) = Real.sqrt 181 ^ 3 := by 
        norm_cast 
      have h13 : (Real.sqrt 181 ^ n : ℝ) = Real.sqrt 181 ^ n := by 
        norm_cast 
      have h14 : Real.sqrt 181 ^ 3 ≤ Real.sqrt 181 ^ n := by 
        have h15 : Real.sqrt 181 ^ (3 : ℝ) ≤ Real.sqrt 181 ^ (n : ℝ) := h11
        norm_cast at h15 ⊢ 
        all_goals linarith 
      linarith 
    linarith [h7, h8, hn_norm]