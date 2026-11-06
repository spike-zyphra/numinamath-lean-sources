import Mathlib

open Real Set
open scoped Real

theorem algebra_301444 {α β : ℝ} (h : sin (α + β) / sin (α - β) = 3) :
    tan α / tan β = 2 := by 
  have h1 : sin (α - β) ≠ 0 := by 
    by_contra h1 
    rw [h1] at h 
    norm_num at h 
  have h2 : sin (α + β) = 3 * sin (α - β) := by 
    field_simp [h1] at h 
    linarith 
  have h3 : sin (α + β) = sin α * cos β + cos α * sin β := by 
    rw [sin_add] 
  have h4 : sin (α - β) = sin α * cos β - cos α * sin β := by 
    rw [sin_sub] 
  rw [h3, h4] at h2 
  have h5 : sin α * cos β = 2 * cos α * sin β := by 
    nlinarith 
  have h6 : cos α ≠ 0 := by 
    by_contra h6 
    have h7 : cos α = 0 := by linarith 
    have h11 : sin α ^ 2 = 1 := by 
      have h12 : sin α ^ 2 + cos α ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq α 
      rw [h7] at h12 
      nlinarith 
    have h8 : sin α = 1 ∨ sin α = -1 := by 
      have h11' : sin α ^ 2 = 1 := h11 
      have : sin α = 1 ∨ sin α = -1 := by 
        rw [sq_eq_one_iff] at h11' 
        assumption 
      assumption 
    have h9 : sin α * cos β = 0 := by 
      rw [h7] at h5 
      nlinarith 
    have h10 : cos β = 0 := by 
      cases h8 with 
      | inl h11 => 
        have : sin α = 1 := h11 
        have : cos β = 0 := by 
          rw [this] at h9 
          nlinarith 
        assumption 
      | inr h11 => 
        have : sin α = -1 := h11 
        have : cos β = 0 := by 
          rw [this] at h9 
          nlinarith 
        assumption 
    have h11 : sin (α - β) = 0 := by 
      rw [h4] 
      rw [h7, h10] 
      norm_num 
    contradiction 
  have h7 : cos β ≠ 0 := by 
    by_contra h7 
    have h8 : cos β = 0 := by linarith 
    have h11 : sin β ^ 2 = 1 := by 
      have h12 : sin β ^ 2 + cos β ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq β 
      rw [h8] at h12 
      nlinarith 
    have h8r : sin α * cos β = 2 * cos α * sin β := by 
      linarith 
    rw [h8] at h8r 
    have h9r : cos α * sin β = 0 := by 
      nlinarith 
    cases (mul_eq_zero.1 h9r) with 
    | inl h13 => 
      have h14 : cos α = 0 := by linarith 
      have h11 : sin (α - β) = 0 := by 
        rw [h4] 
        rw [h14, h8] 
        norm_num 
      contradiction 
    | inr h13 => 
      have h14 : sin β = 0 := by linarith 
      have h11 : sin β ^ 2 = 1 := h11 
      rw [h14] at h11 
      nlinarith 
  have htan1 : tan α = sin α / cos α := by 
    rw [tan_eq_sin_div_cos] 
  have htan2 : tan β = sin β / cos β := by 
    rw [tan_eq_sin_div_cos] 
  rw [htan1, htan2] 
  have htan : (sin α / cos α) / (sin β / cos β) = 2 := by 
    have h8 : cos α ≠ 0 := h6 
    have h9 : sin β ≠ 0 := by 
      by_contra h9 
      have h10 : cos β ≠ 0 := h7 
      have eq1 : sin β = 0 := by linarith [h9]
      have eq2 : sin α * cos β = 0 := by
        rw [eq1] at h5 
        nlinarith 
      cases (mul_eq_zero.1 eq2) with 
      | inl h11 => 
        have h12 : sin α = 0 := by linarith 
        have h13 : sin (α - β) = 0 := by 
          rw [h4]
          rw [h12, eq1]
          norm_num 
        contradiction 
      | inr h11 => 
        have eq2 : cos β = 0 := by linarith 
        contradiction 
    have eq3 : (sin α / cos α) / (sin β / cos β) = (sin α * cos β) / (cos α * sin β) := by 
      field_simp [h6, h9, h7] 
      <;> ring 
    rw [eq3] 
    have eq4 : sin α * cos β = 2 * cos α * sin β := h5 
    have eq5 : (sin α * cos β) / (cos α * sin β) = (2 * cos α * sin β) / (cos α * sin β) := by 
      rw [eq4] 
    rw [eq5] 
    have h10 : cos α ≠ 0 := h6 
    have h11 : sin β ≠ 0 := h9 
    field_simp [h10, h11] 
    <;> nlinarith 
  exact_mod_cast htan