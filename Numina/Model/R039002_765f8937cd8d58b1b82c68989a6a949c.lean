import Mathlib

open Real Set
open scoped Real

theorem algebra_12779 {α : ℝ} (p q : ℝ → Prop)
    (hp : p = fun α => sqrt (1 + sin (2 * α)) = 4 / 3)
    (hq : q = fun α => abs (sin α + cos α) = 4 / 3) :
    p α ↔ q α := by 
  rw [hp, hq]
  constructor
  · -- Assume p, prove q
    intro h
    have h1 : 1 + sin (2 * α) = (16 / 9 : ℝ) := by
      have h2 : sqrt (1 + sin (2 * α)) = (4 / 3 : ℝ) := h
      have h3 : (sqrt (1 + sin (2 * α)) ) ^ 2 = (4 / 3 : ℝ) ^ 2 := by 
        rw [h2]
      have h4 : (sqrt (1 + sin (2 * α)) ) ^ 2 = 1 + sin (2 * α) := by 
        rw [Real.sq_sqrt]
        have h5 : 1 + sin (2 * α) ≥ 0 := by 
          have h6 : -1 ≤ sin (2 * α) := by 
            linarith [neg_one_le_sin (2 * α), sin_le_one (2 * α)]
          linarith
        linarith
      rw [h4] at h3
      nlinarith
    have h2 : sin (2 * α) = (7 / 9 : ℝ) := by 
      linarith [h1]
    have h3 : (sin α + cos α) ^ 2 = (16 / 9 : ℝ) := by
      have h4 : sin (2 * α) = 2 * sin α * cos α := by 
        rw [sin_two_mul]
      rw [h4] at h2
      have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq α
      nlinarith [h2, h5]
    have h4 : abs (sin α + cos α) = (4 / 3 : ℝ) := by 
      have h5 : (sin α + cos α) ^ 2 = (16 / 9 : ℝ) := h3
      have h6 : abs (sin α + cos α) = Real.sqrt ((sin α + cos α) ^ 2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h6, h5]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h4
  · -- Assume q, prove p
    intro h
    have h3 : (sin α + cos α) ^ 2 = (16 / 9 : ℝ) := by 
      have h4 : abs (sin α + cos α) = (4 / 3 : ℝ) := h
      have h5 : (sin α + cos α) ^ 2 = (abs (sin α + cos α)) ^ 2 := by 
        rw [sq_abs]
      rw [h5, h4]
      all_goals norm_num
    have h4 : 1 + sin (2 * α) = (16 / 9 : ℝ) := by
      have h5 : sin (2 * α) = 2 * sin α * cos α := by 
        rw [sin_two_mul]
      have h7 : sin α ^ 2 + cos α ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq α
      nlinarith [Real.sin_sq_add_cos_sq α, h3, h5]
    have h6 : sqrt (1 + sin (2 * α)) = (4 / 3 : ℝ) := by 
      have h7 : 1 + sin (2 * α) = (16 / 9 : ℝ) := h4
      rw [h7]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h6