import Mathlib

open Real

theorem calculus_142809 (f : ℝ → ℝ) (hf : f = fun x => (x ^ ((1 : ℝ) / 3))) (x : ℝ) (hx : x = 8.24) :
    deriv f 8 * (x - 8) + f 8 = 2.02 := by
  have f_def : f = fun x => (x ^ ((1 : ℝ) / 3)) := by exact hf
  have f8 : f 8 = (2 : ℝ) := by
    rw [f_def]
    have h1 : ((8 : ℝ) ^ ((1 : ℝ) / 3)) = (2 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    exact h1

  have df8 : deriv f 8 = (1 / 12 : ℝ) := by
    rw [f_def]
    have hf2 : deriv (fun x : ℝ => x ^ (1 / 3 : ℝ)) 8 = (1 / 12 : ℝ) := by
      simp [deriv_pow]
      have h8p1 : (8 : ℝ) ^ (-2 / 3 : ℝ) = (1 / 4 : ℝ) := by
        have h9 : (8 : ℝ) ^ (-2 / 3 : ℝ) = ((8 : ℝ) ^ (1 / 3 : ℝ)) ^ ( -2 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        have h10 : (8: ℝ)^ (1 / 3 : ℝ) = (2 : ℝ) := by
          have h11 : (8 : ℝ) = (2: ℝ) ^ (3: ℝ) := by norm_num
          rw [h11]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
          all_goals linarith
        have h11 : ((8 : ℝ) ^ (1/3 : ℝ)) ^ (-2 : ℝ) = ((2 : ℝ) )  ^ (-2 : ℝ) := by
          rw [h10]
        have h12 : ((2 : ℝ) : ℝ) ^ (-2 : ℝ) = (1/4 : ℝ) := by
          norm_num
        rw [h9, h11, h12]
      have hxz3 : (8 : ℝ) ^ (3⁻¹ - 1 : ℝ) = (8 : ℝ) ^ (-2 / 3 : ℝ) := by
        have ex1 : (3⁻¹ - 1 : ℝ) = (-2 / 3 : ℝ) := by 
          field_simp
          <;> norm_num
        rw [ex1]
      rw [show (8 : ℝ) ^ (3⁻¹ - 1 : ℝ) = (8 : ℝ) ^ (-2 / 3 : ℝ) by 
          have : (3⁻¹ - 1 : ℝ) = (-2 / 3 : ℝ) := by norm_num
          rw [this]
        ] 
      rw [h8p1]
      all_goals norm_num
    simpa using hf2

  rw [f8, df8, hx]
  all_goals norm_num