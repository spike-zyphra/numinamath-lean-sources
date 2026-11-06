import Mathlib

open Real

theorem algebra_12871 :
    IsGreatest {w : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧ w = x ^ 3 * y ^ 2 * z} (1 / 432) := by
  constructor
  · -- Show that 1/432 is in the set
    use 1 / 2, 1 / 3, 1 / 6
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show that 1/432 is the greatest element in the set
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, h_eq1, hw⟩
    have h1 : x ^ 3 * y ^ 2 * z ≤ 1 / 432 := by
      have h4 : 0 < x := hx
      have h5 : 0 < y := hy
      have h6 : 0 < z := hz
      have h7 : x + y + z = 1 := h_eq1
      have h8 : x ^ 3 * y ^ 2 * z ≤ (1 / 2 : ℝ) ^ 3 * (1 / 3 : ℝ) ^ 2 * (1 / 6 : ℝ) := by
        have h14 : x ^ 3 * y ^ 2 * z = Real.exp (3 * Real.log x + 2 * Real.log y + Real.log z) := by
          have h15 : x ^ 3 * y ^ 2 * z = Real.exp (Real.log (x ^ 3 * y ^ 2 * z)) := by
            rw [Real.exp_log]
            positivity
          have h16 : Real.log (x ^ 3 * y ^ 2 * z) = 3 * Real.log x + 2 * Real.log y + Real.log z := by
            have h17 : Real.log (x ^ 3 * y ^ 2 * z) = Real.log (x ^ 3) + Real.log (y ^ 2) + Real.log (z) := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
            have h18 : Real.log (x ^ 3) = 3 * Real.log x := by
              simp [Real.log_pow]
            have h19 : Real.log (y ^ 2) = 2 * Real.log y := by
              simp [Real.log_pow]
            have h20 : Real.log (z) = Real.log z := by rfl
            rw [h17, h18, h19, h20]
          rw [h16] at h15
          linarith
        have h21 : Real.exp (3 * Real.log x + 2 * Real.log y + Real.log z) ≤ (1 / 2 : ℝ) ^ 3 * (1 / 3 : ℝ) ^ 2 * (1 / 6 : ℝ) := by
          have h25 : 3 * Real.log x + 2 * Real.log y + Real.log z ≤ 3 * Real.log (1 / 2 : ℝ) + 2 * Real.log (1 / 3 : ℝ) + Real.log (1 / 6 : ℝ) := by
            have h29 : Real.log x ≤ Real.log (1 / 2 : ℝ) + 2 * (x - 1 / 2 : ℝ) := by
              have h13 : Real.log (2 * x : ℝ) ≤ (2 * x : ℝ) - 1 := by
                linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * x by nlinarith)]
              have h14 : Real.log (2 * x : ℝ) = Real.log 2 + Real.log x := by
                rw [Real.log_mul (by nlinarith) (by nlinarith)]
              have h15 : Real.log (1 / 2 : ℝ) = Real.log 1 - Real.log 2 := by
                simp [Real.log_div]
              have h16 : Real.log 1 = 0 := Real.log_one
              nlinarith
            have h30 : Real.log y ≤ Real.log (1 / 3 : ℝ) + 3 * (y - 1 / 3 : ℝ) := by
              have h13 : Real.log (3 * y : ℝ) ≤ (3 * y : ℝ) - 1 := by
                linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 * y by nlinarith)]
              have h14 : Real.log (3 * y : ℝ) = Real.log 3 + Real.log y := by
                rw [Real.log_mul (by nlinarith) (by nlinarith)]
              have h15 : Real.log (1 / 3 : ℝ) = Real.log 1 - Real.log 3 := by
                simp [Real.log_div]
              have h16 : Real.log 1 = 0 := Real.log_one
              nlinarith
            have h35 : Real.log z ≤ Real.log (1 / 6 : ℝ) + 6 * (z - 1 / 6 : ℝ) := by
              have h13 : Real.log (6 * z : ℝ) ≤ (6 * z : ℝ) - 1 := by
                linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 * z by nlinarith)]
              have h14 : Real.log (6 * z : ℝ) = Real.log 6 + Real.log z := by
                rw [Real.log_mul (by nlinarith) (by nlinarith)]
              have h15 : Real.log (1 / 6 : ℝ) = Real.log 1 - Real.log 6 := by
                simp [Real.log_div]
              have h16 : Real.log 1 = 0 := Real.log_one
              nlinarith
            have h38 : 3 * Real.log x + 2 * Real.log y + Real.log z ≤ 3 * Real.log (1 / 2 : ℝ) + 2 * Real.log (1 / 3 : ℝ) + Real.log (1 / 6 : ℝ) := by
              nlinarith [h29, h30, h35, show x + y + z = 1 by linarith]
            linarith
          have h20 : Real.exp (3 * Real.log x + 2 * Real.log y + Real.log z) ≤ Real.exp (3 * Real.log (1 / 2 : ℝ) + 2 * Real.log (1 / 3 : ℝ) + Real.log (1 / 6 : ℝ)) := by
            apply Real.exp_le_exp_of_le
            linarith [h25]
          have h21 : Real.exp (3 * Real.log (1 / 2 : ℝ) + 2 * Real.log (1 / 3 : ℝ) + Real.log (1 / 6 : ℝ)) = (1 / 2 : ℝ) ^ 3 * (1 / 3 : ℝ) ^ 2 * (1 / 6 : ℝ) := by
            have h22 : Real.exp (3 * Real.log (1 / 2 : ℝ) + 2 * Real.log (1 / 3 : ℝ) + Real.log (1 / 6 : ℝ)) = Real.exp (3 * Real.log (1 / 2 : ℝ)) * Real.exp (2 * Real.log (1 / 3 : ℝ)) * Real.exp (Real.log (1 / 6 : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]
            have h23 : Real.exp (3 * Real.log (1 / 2 : ℝ)) = (1 / 2 : ℝ) ^ 3 := by
              have h24 : Real.exp (3 * Real.log (1 / 2 : ℝ)) = (Real.exp (Real.log (1 / 2 : ℝ))) ^ 3 := by
                rw [← Real.exp_nat_mul]
                ring
              have h25 : Real.exp (Real.log (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
                rw [Real.exp_log]
                all_goals
                  norm_num
              rw [h25] at h24
              linarith
            have h26 : Real.exp (2 * Real.log (1 / 3 : ℝ)) = (1 / 3 : ℝ) ^ 2 := by
              have h27 : Real.exp (2 * Real.log (1 / 3 : ℝ)) = (Real.exp (Real.log (1 / 3 : ℝ))) ^ 2 := by
                rw [← Real.exp_nat_mul]
                ring
              have h28 : Real.exp (Real.log (1 / 3 : ℝ)) = (1 / 3 : ℝ) := by
                rw [Real.exp_log]
                all_goals
                  norm_num
              rw [h28] at h27
              linarith
            have h29 : Real.exp (Real.log (1 / 6 : ℝ)) = (1 / 6 : ℝ) := by
              rw [Real.exp_log]
              all_goals
                norm_num
            rw [h23, h26, h29] at h22
            linarith
          linarith
        linarith
      have h9 : (1 / 2 : ℝ) ^ 3 * (1 / 3 : ℝ) ^ 2 * (1 / 6 : ℝ) = (1 / 432 : ℝ) := by norm_num
      linarith [h9, h8]
    have h2 : w ≤ 1 / 432 := by
      linarith [hw, h1]
    linarith