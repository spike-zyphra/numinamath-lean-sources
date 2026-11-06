import Mathlib

open Real Set
open scoped Real

theorem algebra_241493 :
    IsGreatest { 2 * sin (x / 2) * (1 - sin (x / 2)) * (1 + sin (x / 2)) ^ 2 | (x : ℝ) (_ : 0 ≤ x) (_ : x ≤ π)} ((107 + 51 * √17)/256) := by
  constructor
  · -- Show that (107 + 51 * Real.sqrt 17) / 256 is in the set.
    use 2 * arcsin ((1 + Real.sqrt 17) / 8)
    have ht1 : 0 ≤ (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) := by
      have h1 : arcsin ((1 + Real.sqrt 17) / 8) ≥ 0 := by
        apply arcsin_nonneg.mpr 
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      linarith 
    have ht2 : (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) ≤ Real.pi := by
      have h2 : arcsin ((1 + Real.sqrt 17) / 8) ≤ Real.pi / 2 := by 
        apply arcsin_le_pi_div_two 
      linarith
    have ht3 : sin ( (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) / 2 ) = (1 + Real.sqrt 17) / 8 := by 
      have h5 : (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) / 2 = arcsin ((1 + Real.sqrt 17) / 8) := by ring 
      rw [h5] 
      have h6 : sin (arcsin ((1 + Real.sqrt 17) / 8)) = (1 + Real.sqrt 17) / 8 := by
        apply sin_arcsin 
        · -- Show that -1 ≤ (1 + Real.sqrt 17) / 8
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
        · -- Show that (1 + Real.sqrt 17) / 8 ≤ 1 
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      linarith 
    have ht4 : 2 * sin ( (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) / 2 ) * (1 - sin ( (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) / 2 )) * (1 + sin ( (2 * arcsin ((1 + Real.sqrt 17) / 8) : ℝ) / 2 )) ^ 2 = (107 + 51 * Real.sqrt 17) / 256 := by 
      rw [ht3] 
      field_simp 
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    simp_all [ht1, ht2, ht4] 
  · -- Show that it is greatest.
    intro y hy
    rcases hy with ⟨x, hx1, hx2, h_eq⟩ 
    have hx3 : sin (x / 2) ≥ 0 := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      · -- Show that 0 ≤ x / 2
        linarith 
      · -- Show that x / 2 ≤ Real.pi
        linarith 
    have hx4 : sin (x / 2) ≤ 1 := by 
      apply sin_le_one
    have ht5 : 2 * sin (x / 2) * (1 - sin (x / 2)) * (1 + sin (x / 2)) ^ 2 ≤ (107 + 51 * Real.sqrt 17) / 256 := by 
      have h1 : sin (x / 2) ≥ 0 := hx3 
      have h2 : sin (x / 2) ≤ 1 := hx4 
      nlinarith [sq_nonneg (sin (x / 2) - (1 + Real.sqrt 17) / 8), sq_nonneg (sin (x / 2) - (1 - Real.sqrt 17) / 8), sq_nonneg (sin (x / 2) + (1 + Real.sqrt 17) / 8), sq_nonneg (sin (x / 2) -1),
        Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num),
        sq_nonneg (sin (x / 2) * (sin (x / 2) - (1 + Real.sqrt 17) / 8)), sq_nonneg ((sin (x / 2) - 1) * (sin (x / 2) + 1)), mul_nonneg h1 (show (0 : ℝ) ≤ (1 - sin (x / 2) : ℝ) by nlinarith [sq_nonneg (sin (x / 2) -1), Real.sin_sq_add_cos_sq (x / 2)])
        ]
    linarith [h_eq, ht5]