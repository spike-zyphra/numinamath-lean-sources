import Mathlib

open Real

theorem number_theory_301021 {a b c d : ℝ}
    (ha : a = ⌊sqrt 2⌋) (hb : b = sqrt 2 - a)
    (hc : c = ⌊Real.pi⌋) (hd : d = Real.pi - c) :
    a * d - b * c ∈ Set.Ioo (-2) (-1) := by
  have ha1 : a = 1 := by
    rw [ha]
    have h1 : ⌊sqrt 2⌋ = 1 := by
      have h2 : 1 < sqrt 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h3 : sqrt 2 < 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    exact_mod_cast h1
  have hb1 : b = sqrt 2 - 1 := by
    rw [hb, ha1]
  have hc1 : c = 3 := by
    rw [hc]
    have h1 : ⌊Real.pi⌋ = 3 := by
      have h2 : 3 < Real.pi := by linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h3 : Real.pi < 4 := by linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    exact_mod_cast h1
  have hd1 : d = Real.pi - 3 := by
    rw [hd, hc1]
  rw [Set.mem_Ioo]
  rw [ha1, hb1, hc1, hd1]
  constructor
  · -- Show that $-2 < \pi - 3 \sqrt{2}$.
    nlinarith [Real.sqrt_nonneg 2, Real.pi_gt_31415, Real.pi_lt_31416, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show that $\pi - 3 \sqrt{2} < -1$.
    nlinarith [Real.sqrt_nonneg 2, Real.pi_gt_31415, Real.pi_lt_31416, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]