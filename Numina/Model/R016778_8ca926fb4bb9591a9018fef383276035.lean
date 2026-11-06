import Mathlib

open Real Set
open scoped Real

theorem algebra_326219 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : cos (α + β) = -4 / 5) (x : ℝ) (hx : sin β = x) (y : ℝ) (hy : cos α = y) :
    y = -4 / 5 * sqrt (1 - x ^ 2) + 3 / 5 * x ∧ x ∈ Ioo (4 / 5) 1 := by 
  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hβ1, hβ2⟩
  have h3 : cos (α + β) = cos α * cos β - sin α * sin β := by 
    rw [cos_add]
  rw [h3] at h₂
  have h4 : sin β = x := hx
  have h5 : cos α = y := hy
  have h6 : cos β = Real.sqrt (1 - x ^ 2) := by
    have h7 : cos β ^ 2 + sin β ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq β
    rw [show sin β = x by linarith [h4]] at h7
    have h8 : cos β ^ 2 = 1 - x ^ 2 := by linarith
    have h9 : cos β > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [hβ1, hβ2, Real.pi_pos]
    have h10 : cos β = Real.sqrt (1 - x ^ 2) := by
      rw [← h8]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_pos h9]
      all_goals nlinarith
    exact h10
  have h11 : sin α = Real.sqrt (1 - y ^ 2) := by
    have h12 : cos α ^ 2 + sin α ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq α
    rw [show cos α = y by linarith [h5]] at h12
    have h13 : sin α ^ 2 = 1 - y ^ 2 := by linarith
    have h14 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hα1, hα2, Real.pi_pos]
      linarith [hα1, hα2, Real.pi_pos]
    have h15 : sin α = Real.sqrt (1 - y ^ 2) := by
      rw [← h13]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_pos h14]
      all_goals nlinarith
    exact h15
  rw [h5, h6, h11, hx] at h₂
  have h7 : 0 < x := by
    have h8 : sin β > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hβ1, hβ2, Real.pi_pos]
      linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hx, h8]
  have h8 : x < 1 := by
    have h9 : sin β < 1 := by
      have h10 : sin β < sin (π / 2) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [hβ1, hβ2, Real.pi_pos]
      have h11 : sin (π / 2) = 1 := Real.sin_pi_div_two
      linarith [h10, h11]
    linarith [hx, h9]
  have h9 : 0 < y := by
    have h10 : cos α > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [hα1, hα2, Real.pi_pos]
    linarith [hy, h10]
  have h10 : y < 1 := by
    have h11 : cos α < 1 := by
      have h12 : cos α < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [hα1, hα2, Real.pi_pos]
      have h13 : cos (0 : ℝ) = 1 := Real.cos_zero
      linarith [h12, h13]
    linarith [hy, h11]
  have h12 : sin (α + β) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    have h13 : α + β > 0 := by nlinarith [hα1, hβ1, Real.pi_pos]
    linarith [h13, Real.pi_pos]
    have h14 : α + β < Real.pi := by
      nlinarith [hα2, hβ2, Real.pi_pos]
    linarith [h14, Real.pi_pos]
  have h13 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h13] at h12
  rw [h5, h6, h11, hx] at h12
  have hx1 : 0 < Real.sqrt (1 - x ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith 
  have hy1 : 0 < Real.sqrt (1 - y ^ 2) := by 
    apply Real.sqrt_pos.mpr
    nlinarith 
  have h14 : x > 4 / 5 := by
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y ^ 2 by nlinarith), 
      mul_pos hx1 (show 0 < (y : ℝ) by nlinarith), 
      mul_pos hy1 (show 0 < (x : ℝ) by nlinarith)
    ]
  have h15 : x < 1 := by
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y ^ 2 by nlinarith), 
      mul_pos hx1 (show 0 < (y : ℝ) by nlinarith), 
      mul_pos hy1 (show 0 < (x : ℝ) by nlinarith)
    ]
  have h16 : y = -4 / 5 * sqrt (1 - x ^ 2) + 3 / 5 * x := by 
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y ^ 2 by nlinarith), 
      mul_pos hx1 hy1
    ]
  constructor
  · exact h16
  · constructor
    · exact_mod_cast h14
    · exact_mod_cast h15