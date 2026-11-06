import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_164676 (x : ℝ) (hx : x ∈ Ioo 0 Real.pi) :
    (logb 10 20)^(2 * cos x) > 1 ↔ x ∈ Ioo 0 (π/2) := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Show $(\logb 10 20)^{2 * \cos x} > 1$ implies $x \in (0, \pi/2)$
    intro h
    have h1 : logb 10 20 > 1 := by
      have h2 : logb 10 20 = logb 10 2 + 1 := by
        calc
          logb 10 20 = logb 10 (2 * 10) := by norm_num
          _ = logb 10 2 + logb 10 10 := by rw [logb_mul (by norm_num) (by norm_num)]
          _ = logb 10 2 + 1 := by simp
      rw [h2]
      have h3 : logb 10 2 > 0 := by
        apply logb_pos
        all_goals norm_num
      linarith
    have h2 : 2 * cos x > 0 := by 
      by_contra h3
      push_neg at h3 
      have h5 : (logb 10 20 : ℝ) ^ (2 * cos x) ≤ (1 : ℝ) := by
        have h51 : (logb 10 20 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by simp 
        have h52 : (logb 10 20 : ℝ) ^ (2 * cos x) ≤ (logb 10 20 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le 
          all_goals linarith 
        rw [h51] at h52 
        linarith 
      have h51 : (logb 10 20 : ℝ) ^ (2 * cos x) > (1 : ℝ) := by 
        linarith 
      linarith 
    have hcos : cos x > 0 := by linarith 
    have hx3 : x < Real.pi / 2 := by
      by_contra h3
      push_neg at h3 
      have h5 : cos x ≤ 0 := by 
        have h51 : Real.pi / 2 ≤ x := by linarith 
        have h52 : cos x ≤ 0 := by
          apply cos_nonpos_of_pi_div_two_le_of_le 
          all_goals linarith 
          all_goals linarith 
        linarith 
      linarith [hcos, h5] 
    constructor <;> (try linarith) <;> try nlinarith 
  · -- Show x ∈ (0, π/2) implies $(\logb 10 20)^{2 * \cos x} > 1$
    intro h
    rcases h with ⟨hx3, hx4⟩ 
    have h1 : logb 10 20 > 1 := by
      have h2 : logb 10 20 = logb 10 2 + 1 := by
        calc 
          logb 10 20 = logb 10 (2 * 10) := by norm_num 
          _ = logb 10 2 + logb 10 10 := by rw [logb_mul (by norm_num) (by norm_num)]
          _ = logb 10 2 + 1 := by simp 
      rw [h2]
      have h3 : logb 10 2 > 0 := by
        apply logb_pos 
        all_goals norm_num 
      linarith 
    have hcos : cos x > 0 := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> (try linarith) <;> try nlinarith 
    have h2 : 2 * cos x > 0 := by 
      linarith 
    -- Since the base logb 10 20 > 1 and the exponent is positive
    have h3 : (logb 10 20)^(2 * cos x) > (1 : ℝ) := by
      have h4 : (logb 10 20 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by 
        simp 
      have h5 : (logb 10 20 : ℝ) ^ (2 * cos x) > (logb 10 20 : ℝ) ^ (0 : ℝ) := by 
        apply Real.rpow_lt_rpow_of_exponent_lt 
        all_goals linarith 
      rw [h4] at h5 
      linarith 
    linarith 
    all_goals linarith 
    all_goals nlinarith 
    all_goals nlinarith