import Mathlib

theorem number_theory_13656 : round ((1020201 : ℝ) ^ ((1 : ℝ) / 3)) = 101 := by
  have h1 : (1020201 : ℝ) ^ ((1 : ℝ) / 3) < (101.5 : ℝ) := by
    have h2 : (1020201 : ℝ) < (101.5 : ℝ) ^ 3 := by
      norm_num
    have h3 : ( (1020201 : ℝ) ^ ((1 : ℝ) / 3) ) < ( (101.5 : ℝ) ) := by
      have h4 : ( (1020201 : ℝ) ) < ( (101.5 : ℝ) ^ 3 ) := by
        norm_num
      have h5 : ( (1020201 : ℝ) ^ ((1 : ℝ) / 3) ) < ( ( (101.5 : ℝ) ^ 3 ) ^ ((1 : ℝ) / 3) ) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith
      have h6 : ( ( (101.5 : ℝ) ^ 3 ) ^ ((1 : ℝ) / 3) ) = ( (101.5 : ℝ) ) := by
        have h7 : (101.5 : ℝ) ≥ 0 := by
          norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      linarith
    linarith

  have h2 : (100.5 : ℝ) < (1020201 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h3 : ( (100.5 : ℝ) ) ^ 3 < ( (1020201 : ℝ) ) := by
      norm_num
    have h4 : ( (100.5 : ℝ) ) < ( (1020201 : ℝ) ^ ((1 : ℝ) / 3) ) := by
      have h5 : ( ( (100.5 : ℝ) ) ^ 3 ) < ( (1020201 : ℝ) ) := by
        norm_num
      have h6 : ( ( (100.5 : ℝ) ) ^ 3 ) ^ ((1 : ℝ) / 3) < ( (1020201 : ℝ) ^ ((1 : ℝ) / 3) ) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith
      have h7 : ( ( (100.5 : ℝ) ) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (100.5 : ℝ) ) := by
        have h8 : (100.5 : ℝ) ≥ 0 := by
          norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      linarith
    linarith

  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith