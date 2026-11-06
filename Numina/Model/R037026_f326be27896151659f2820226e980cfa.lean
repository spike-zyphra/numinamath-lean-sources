import Mathlib

open BigOperators Complex Filter Finset Real Set TopologicalSpace Topology

theorem calculus_16348 (a b : EuclideanSpace ℝ (Fin 3))
  (ha : a = ![2, -1, 1]) (hb : b = ![-1, 1, 0]) :
  arccos (inner a b / (norm a * norm b)) * 180 / π = 150 := by
  rw [ha, hb]
  simp [Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h1 : arccos (-Real.sqrt 3 / 2) = 5 * Real.pi / 6 := by
    have h2 : Real.cos (5 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
      have h3 : 5 * Real.pi / 6 = Real.pi - (Real.pi / 6) := by
        ring
      rw [h3]
      have h4 : Real.cos (Real.pi - (Real.pi / 6)) = -Real.cos (Real.pi / 6) := by
        rw [Real.cos_pi_sub]
      rw [h4]
      have h5 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      rw [h5]
      all_goals
        ring
    have h3 : 0 ≤ 5 * Real.pi / 6 := by
      nlinarith [Real.pi_pos]
    have h4 : 5 * Real.pi / 6 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    rw [←h2]
    apply Real.arccos_cos
    all_goals
      nlinarith [Real.pi_pos]
  have h2 : arccos (-3 / (Real.sqrt 6 * Real.sqrt 2)) = 5 * Real.pi / 6 := by
    have h3 : -3 / (Real.sqrt 6 * Real.sqrt 2) = -Real.sqrt 3 / 2 := by
      have h4 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
        have h5 : Real.sqrt 6 * Real.sqrt 2 = Real.sqrt 12 := by
          rw [show (12 : ℝ) = (6 : ℝ) * (2 : ℝ) by norm_num]
          rw [Real.sqrt_mul (by norm_num)]
        rw [h5]
        have h7 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        linarith
      rw [h4]
      have h10 : -3 / (2 * Real.sqrt 3) = -Real.sqrt 3 / 2 := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    rw [h3]
    linarith [h1]
  have h3 : arccos (-3 / (Real.sqrt 6 * Real.sqrt 2)) * 180 / Real.pi = 150 := by
    rw [h2]
    field_simp
    <;> nlinarith [Real.pi_pos, Real.pi_gt_three]
  nlinarith