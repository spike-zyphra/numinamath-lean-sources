import Mathlib

theorem number_theory_13521 (x : ℝ) (hx : x = (1022612) ^ ((1 : ℝ) / 4)) :
    round x = 32 := by
  have h1 : 31.5 < x := by
    rw [hx]
    have h2 : (31.5 : ℝ) ^ (4 : ℝ) < (1022612 : ℝ) := by
      norm_num
    have h3 : (31.5 : ℝ) < (1022612 : ℝ) ^ ((1 : ℝ) / 4) := by
      have h4 : ( (31.5 : ℝ) ^ (4 : ℝ) ) < (1022612 : ℝ) := by
        norm_num
      have h6 : ( (31.5 : ℝ) ^ (4 : ℝ) ) ^ ((1 : ℝ) / 4) = (31.5 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h7 : ( (31.5 : ℝ) ^ (4 : ℝ) ) ^ ((1 : ℝ) / 4) < (1022612 : ℝ) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_lt_rpow
        all_goals
        nlinarith [show (31.5 : ℝ) ^ (4 : ℝ) < (1022612 : ℝ) by norm_num]
      nlinarith [h6, h7, show (31.5 : ℝ) ^ (4 : ℝ) < (1022612 : ℝ) by norm_num]
    linarith
  have h2 : x < (32.5 : ℝ) := by
    rw [hx]
    have h4 : (1022612 : ℝ) < (32.5 : ℝ) ^ (4 : ℝ) := by
      norm_num
    have h8 : (1022612 : ℝ) ^ ((1 : ℝ) / 4) < (32.5 : ℝ) := by
      have h9 : (1022612 : ℝ) < ( (32.5 : ℝ) ^ (4 : ℝ) ) := by
        norm_num
      have h10 : ( (32.5 : ℝ) ^ (4 : ℝ) ) ^ ((1 : ℝ) / 4) = (32.5 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h11 : (1022612 : ℝ) ^ ((1 : ℝ) / 4) < ( (32.5 : ℝ) ^ (4 : ℝ) ) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_lt_rpow
        all_goals
        nlinarith [show (1022612 : ℝ) < ( (32.5 : ℝ) ^ (4 : ℝ) ) by norm_num]
      nlinarith [h10, h11, show (1022612 : ℝ) < ( (32.5 : ℝ) ^ (4 : ℝ) ) by norm_num]
    linarith
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith