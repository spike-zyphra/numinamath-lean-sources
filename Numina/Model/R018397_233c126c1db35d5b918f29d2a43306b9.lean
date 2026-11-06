import Mathlib

theorem algebra_285 {t : ℝ} (ht : t = 1 / (2 - Real.sqrt 3)) (a b : ℝ)
    (ha : a = t - ⌊t⌋) (hb : b = -t - ⌊-t⌋) :
    1 / (2 * b) - 1 / a = 1 / 2 := by

  have ht_eq : t = 2 + Real.sqrt 3 := by 
    rw [ht]
    have h1 : 2 - Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h2 : 1 / (2 - Real.sqrt 3) = 2 + Real.sqrt 3 := by
      field_simp [(show 2 - Real.sqrt 3 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
    rw [h2]

  have ht_floor : ⌊t⌋ = 3 := by
    rw [ht_eq]
    have h1 : 3 < 2 + Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h2 : 2 + Real.sqrt 3 < 4 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith

  have hnt_floor : ⌊-t⌋ = -4 := by
    have ht_eq' : -t = - (2 + Real.sqrt 3) := by
      rw [ht_eq]
      all_goals ring
    rw [ht_eq']
    have h3 : - (2 + Real.sqrt 3) > -4 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 : - (2 + Real.sqrt 3) < -3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith

  have ha_eq : a = Real.sqrt 3 - 1 := by
    rw [ha, ht_floor]
    have ht_eq' : t = 2 + Real.sqrt 3 := ht_eq
    rw [ht_eq']
    all_goals ring_nf

  have hb_eq : b = 2 - Real.sqrt 3 := by
    rw [hb, hnt_floor]
    have ht_eq' : t = 2 + Real.sqrt 3 := ht_eq
    rw [ht_eq']
    all_goals ring_nf

  rw [hb_eq, ha_eq]

  have ha_pos : Real.sqrt 3 - 1 > 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have hb_pos : (2 - Real.sqrt 3) > 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  field_simp [(show (2 - Real.sqrt 3) ≠ 0 by linarith), (show Real.sqrt 3 - 1 ≠ 0 by linarith)]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]