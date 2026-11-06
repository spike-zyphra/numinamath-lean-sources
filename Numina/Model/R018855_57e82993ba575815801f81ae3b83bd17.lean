import Mathlib

open Real Set

theorem algebra_325189 (α β : ℝ) (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2))
    (h : sin β = 2 * cos (α + β) * sin α) (h' : α + β ≠ π/2) :
    tan β ≤ sqrt 3 / 3 := by
  rcases hα with ⟨hα1, hα2⟩
  rcases hβ with ⟨hβ1, hβ2⟩
  have h1 : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  rw [h1] at h
  have hcosβ : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]
  have hsinβ : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]
  have hcosα : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]
  have hsinα : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]
  have eq1 : sin β * (1 + 2 * sin α ^ 2) = 2 * cos α * sin α * cos β := by
    nlinarith [h, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  have htan : tan β = sin (2 * α) / (2 - cos (2 * α)) := by
    have eq2 : sin β * (1 + 2 * sin α ^ 2) = 2 * cos α * sin α * cos β := eq1
    have h2 : 1 + 2 * sin α ^ 2 = 2 - cos (2 * α) := by
      have h3 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
        rw [cos_two_mul, sin_sq]
        ring
      linarith [h3]
    have h4 : 2 * cos α * sin α = sin (2 * α) := by
      have h5 : sin (2 * α) = 2 * sin α * cos α := by
        rw [sin_two_mul]
      nlinarith [h5]
    have eq2' : sin β * (2 - cos (2 * α)) = sin (2 * α) * cos β := by
      rw [show 1 + 2 * sin α ^ 2 = 2 - cos (2 * α) by linarith [h2]] at eq1
      rw [show 2 * cos α * sin α = sin (2 * α) by linarith [h4]] at eq1
      linarith [eq1]
    have htan2 : tan β = sin (2 * α) / (2 - cos (2 * α)) := by
      have htan : tan β = sin β / cos β := by
        rw [tan_eq_sin_div_cos]
      rw [htan]
      have hx2 : 2 - cos (2 * α) ≠ 0 := by
        have h13 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
          rw [cos_two_mul, sin_sq]
          ring
        rw [h13]
        nlinarith [hsinα]
      have eq3 : sin β / cos β = sin (2 * α) / (2 - cos (2 * α)) := by
        have eq2' : sin β * (2 - cos (2 * α)) = sin (2 * α) * cos β := eq2'
        have hx1 : 2 - cos (2 * α) ≠ 0 := by
          have h13 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by
            rw [cos_two_mul, sin_sq]
            ring
          rw [h13]
          nlinarith [hsinα]
        have hx3 : cos β > 0 := hcosβ
        field_simp [show cos β ≠ 0 by nlinarith, hx1]
        linarith [eq2']
      exact eq3
    exact htan2
  rw [htan]
  have h2 : sin (2 * α) / (2 - cos (2 * α)) ≤ Real.sqrt 3 / 3 := by
    have h5 : sin (2 * α) * 3 ≤ Real.sqrt 3 * (2 - cos (2 * α)) := by
      have h3 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (2 * α)
      have h4 : Real.sqrt 3 ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [sq_nonneg (sin (2 * α) - Real.sqrt 3 / 2), sq_nonneg (cos (2 * α) - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), sq_nonneg (sin (2 * α) * Real.sqrt 3 - cos (2 * α) * 1)]
    have h9 : 2 - cos (2 * α) > 0 := by
      have h10 : cos (2 * α) ≤ 1 := by
        exact Real.cos_le_one (2 * α)
      nlinarith [Real.neg_one_le_cos (2 * α)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h5]
  linarith [h2]