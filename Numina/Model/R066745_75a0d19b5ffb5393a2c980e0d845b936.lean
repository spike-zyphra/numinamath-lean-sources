import Mathlib

theorem algebra_209216 (x : ℝ) :
    x^2 - x - Real.sin (Real.pi * x) = -1.25 ↔ x = 0.5 := by
  constructor
  · -- Assume x^2 - x - Real.sin (Real.pi * x) = -1.25, prove x = 0.5
    intro h
    have h1 : x^2 - x + 1.25 = Real.sin (Real.pi * x) := by
      linarith [h]
    have h2 : x^2 - x + 1.25 ≥ 1 := by
      nlinarith [sq_nonneg (x - 0.5)]
    have h3 : Real.sin (Real.pi * x) ≤ 1 := by
      apply Real.sin_le_one
    have h6 : Real.sin (Real.pi * x) = 1 := by
      linarith [h1, h2, h3]
    obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h6
    have hk' : Real.pi * x = Real.pi / 2 + ↑k * (2 * Real.pi) := by
      nlinarith
    have hk_eq : x = (1/2 : ℝ) + (2 : ℝ) * ((k : ℝ)) := by
      have hpi : Real.pi ≠ 0 := by
        linarith [Real.pi_pos]
      have h7 : ↑k * (2 * Real.pi) = ↑k * 2 * Real.pi := by ring
      nlinarith [hk', Real.pi_pos]
    rw [hk_eq] at h1
    have h7 : ( (1/2 : ℝ) + 2 * ((k : ℝ)) )^2 - ( (1/2 : ℝ) + 2 * ((k : ℝ)) ) + 1.25 = 1 := by
      nlinarith [Real.sin_le_one (Real.pi * ((1/2 : ℝ) + 2 * ((k : ℝ)) )), sq_nonneg (( (1/2 : ℝ) + 2 * ((k : ℝ)) ) - 0.5)]
    have hk0 : (k : ℝ) = 0 := by
      have eq1 : ( (1/2 : ℝ) + 2 * ((k : ℝ)) )^2 - ( (1/2 : ℝ) + 2 * ((k : ℝ)) ) + 1.25 = 1 := by
        nlinarith [h7]
      ring_nf at eq1 ⊢
      nlinarith [sq_nonneg ((k : ℝ)), Real.sin_le_one (Real.pi * ((1/2 : ℝ) + 2 * ((k : ℝ)) ))]
    have hk_int : k = 0 := by
      exact_mod_cast hk0
    have hx : x = 0.5 := by
      rw [hk_eq]
      rw [show (k : ℝ) = (0 : ℝ) by exact_mod_cast hk_int]
      norm_num
    linarith [hx]
  · -- Assume x = 0.5, prove x^2 - x - Real.sin (Real.pi * x) = -1.25
    intro h
    rw [h]
    have h1 : Real.sin (Real.pi * (0.5 : ℝ)) = 1 := by 
      have h2 : Real.pi * (0.5 : ℝ) = Real.pi / 2 := by ring_nf
      rw [h2]
      norm_num [Real.sin_pi_div_two]
    nlinarith [Real.sin_le_one (Real.pi * (0.5 : ℝ)), h1]