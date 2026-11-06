import Mathlib

open Real Set
open scoped Real

theorem algebra_10137 :
  IsLeast {x | ∃ t : ℝ, x = sin t ^ 4 + 2 * sin t * cos t + cos t ^ 4} (-1/2) := by
  constructor
  · -- Show that -1/2 is achieved
    use 3 * Real.pi / 4
    have hsin : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      have h1 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by
        linarith [Real.pi_pos]
      rw [h1]
      rw [sin_pi_sub]
      rw [sin_pi_div_four]
      <;> ring_nf <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have hcos : cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h1 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by
        linarith [Real.pi_pos]
      rw [h1]
      rw [cos_pi_sub]
      rw [cos_pi_div_four]
      <;> ring_nf <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    rw [hsin, hcos]
    have h2 : Real.sqrt 2 ^ 4 = (4 : ℝ) := by 
      calc 
        Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
        _ = (2) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
        _ = (4 : ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
      sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 2 ^ 2 + 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that -1/2 is the smallest
    intro x
    rintro ⟨t, ht⟩
    have ht1 : sin t ^ 2 + cos t ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq t
    have ht3 : sin t ^ 4 + cos t ^ 4 = 1 - 2 * (sin t * cos t) ^ 2 := by
      have h2 : sin t ^ 2 + cos t ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq t
      calc
        sin t ^ 4 + cos t ^ 4 = (sin t ^ 2 + cos t ^ 2) ^ 2 - 2 * (sin t * cos t) ^ 2 := by 
          nlinarith [sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t * cos t), Real.sin_sq_add_cos_sq t]
        _ = 1 ^ 2 - 2 * (sin t * cos t) ^ 2 := by rw [h2]
        _ = 1 - 2 * (sin t * cos t) ^ 2 := by 
          ring
    have ht4 : sin t * cos t ≤ 1 / 2 := by
      have h2 : sin t ^ 2 + cos t ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq t
      nlinarith [sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t * cos t), Real.sin_sq_add_cos_sq t]
    have ht5 : - (1 / 2) ≤ sin t * cos t := by
      have h2 : sin t ^ 2 + cos t ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq t
      nlinarith [sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t * cos t), Real.sin_sq_add_cos_sq t]
    nlinarith [ht, ht3, Real.sin_le_one t, Real.cos_le_one t, Real.sin_le_one t, Real.sin_le_one t, sq_nonneg (sin t - cos t), sq_nonneg (sin t * cos t), ht4, ht5, Real.sin_le_one t, Real.cos_le_one t]