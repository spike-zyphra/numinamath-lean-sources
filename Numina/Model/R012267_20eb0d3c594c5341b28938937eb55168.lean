import Mathlib

set_option maxHeartbeats 400000

theorem algebra_221530 (a b c d : ℝ) (ha : |a| > 1) (hb : |b| > 1) (hc : |c| > 1) (hd : |d| > 1)
    (h : a * b * c + a * b * d + a * c * d + b * c * d + a + b + c + d = 0) :
    0 < 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) := by

  let x := (a + 1) / (a - 1)
  let y := (b + 1) / (b - 1)
  let z := (c + 1) / (c - 1)
  let t := (d + 1) / (d - 1)
  have x_pos_of_abs_a_gt_1 {a : ℝ} (ha : |a| > 1) : (a + 1) / (a - 1) > 0 := by
    by_cases w_a_nonneg : a ≥ 0
    . have : |a| = a := by
        exact abs_of_nonneg w_a_nonneg
      rw [this] at ha
      have a_sub_1_pos : a - 1 > 0 := by
        linarith
      have a_add_1_pos : a + 1 > 0 := by
        linarith
      exact div_pos a_add_1_pos a_sub_1_pos
    . simp at w_a_nonneg
      have : |a| = -a := by
        exact abs_of_neg w_a_nonneg
      rw [this] at ha
      have a_sub_1_neg : a - 1 < 0 := by
        linarith
      have a_add_1_neg : a + 1 < 0 := by
        linarith
      exact div_pos_of_neg_of_neg a_add_1_neg a_sub_1_neg
  have hx1 : x > 0 := x_pos_of_abs_a_gt_1 ha
  have hy1 : y > 0 := x_pos_of_abs_a_gt_1 hb
  have hz1 : z > 0 := x_pos_of_abs_a_gt_1 hc
  have ht1 : t > 0 := x_pos_of_abs_a_gt_1 hd
  have sub_1_eq_0_of_abs_gt_1 {a : ℝ} (ha : |a| > 1) : a - 1 ≠ 0 := by
    intro eq
    have : a = 1 := by
      linarith
    rw [this] at ha
    norm_num at ha
  have ha1 : a - 1 ≠ 0 := sub_1_eq_0_of_abs_gt_1 ha
  have hb1 : b - 1 ≠ 0 := sub_1_eq_0_of_abs_gt_1 hb
  have hc1 : c - 1 ≠ 0 := sub_1_eq_0_of_abs_gt_1 hc
  have hd1 : d - 1 ≠ 0 := sub_1_eq_0_of_abs_gt_1 hd
  have h1 : 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) = (x + y + z + t - 4) / 2 := by
    unfold x y z t
    field_simp
    ring
  rw [h1]
  have h5 : x * y * z * t = 1 := by
    unfold x y z t
    field_simp
    nlinarith
  have h7 : x + y + z + t - 4 > 0 := by
    have h8 : (a - 1) ≠ 0 := ha1 
    have h9 : (b - 1) ≠ 0 := hb1 
    have h10 : (c - 1) ≠ 0 := hc1 
    have h11 : (d - 1) ≠ 0 := hd1 
    have h12 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 + (t - 1) ^ 2 > 0 := by 
      have h13 : x - 1 ≠ 0 := by 
        by_contra h_eq
        have : (a + 1) / (a - 1) = 1 := by linarith [show x = (a + 1) / (a - 1) by rfl, h_eq]
        have : a = 0 := by 
          field_simp [(show a - 1 ≠ 0 by exact ha1)] at this 
          linarith 
        have : |a| = 0 := by 
          rw [this]
          norm_num 
        linarith 
      have h14 : y - 1 ≠ 0 := by 
        by_contra h_eq 
        have : (b + 1) / (b - 1) = 1 := by linarith [show y = (b + 1) / (b - 1) by rfl, h_eq] 
        have : b = 0 := by 
          field_simp [(show b - 1 ≠ 0 by exact hb1)] at this 
          linarith 
        have : |b| = 0 := by 
          rw [this] 
          norm_num 
        linarith 
      have h15 : z - 1 ≠ 0 := by 
        by_contra h_eq 
        have : (c + 1) / (c - 1) = 1 := by linarith [show z = (c + 1) / (c - 1) by rfl, h_eq] 
        have : c = 0 := by 
          field_simp [(show c - 1 ≠ 0 by exact hc1)] at this 
          linarith 
        have : |c| = 0 := by 
          rw [this] 
          norm_num 
        linarith 
      have h16 : t - 1 ≠ 0 := by 
        by_contra h_eq 
        have : (d + 1) / (d - 1) = 1 := by linarith [show t = (d + 1) / (d - 1) by rfl, h_eq] 
        have : d = 0 := by 
          field_simp [(show d - 1 ≠ 0 by exact hd1)] at this 
          linarith 
        have : |d| = 0 := by 
          rw [this] 
          norm_num 
        linarith 
      have hx16 : (x - 1) ^ 2 > 0 := by 
        apply sq_pos_of_ne_zero 
        exact h13 
      have hy16 : (y - 1) ^ 2 > 0 := by 
        apply sq_pos_of_ne_zero 
        exact h14 
      have hz16 : (z - 1) ^ 2 > 0 := by 
        apply sq_pos_of_ne_zero 
        exact h15 
      have ht16 : (t - 1) ^ 2 > 0 := by 
        apply sq_pos_of_ne_zero 
        exact h16 
      linarith [hx16, hy16, hz16, ht16] 
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (x * t - 1), sq_nonneg (y * z - 1), sq_nonneg (y * t - 1), sq_nonneg (z * t - 1), 
      mul_pos hx1 hy1, mul_pos hx1 hz1, mul_pos hx1 ht1, 
      mul_pos hy1 hz1, mul_pos hy1 ht1, mul_pos hz1 ht1, h5
    ] 
  linarith