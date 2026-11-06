import Mathlib

theorem algebra_111310 {x : ℝ} (hx : x = 2 ^ ((1 : ℝ) / 3) + 3 ^ ((1 : ℝ) / 3)) :
    x ^ 9 - 15 * x ^ 6 - 87 * x ^ 3 - 125 = 0 := by 
  have h1 : x = (2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ) := by linarith [hx]
  rw [h1]
  have h2 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h3 : ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h4 : ((2 : ℝ) ^ (1 / 3 : ℝ)) * ((3 : ℝ) ^ (1 / 3 : ℝ)) = (6 : ℝ) ^ (1 / 3 : ℝ) := by
    have h5 : ((2 : ℝ) ^ (1 / 3 : ℝ)) * ((3 : ℝ) ^ (1 / 3 : ℝ)) = ((2 * 3 : ℝ) ^ (1 / 3 : ℝ)) := by
      rw [← Real.mul_rpow]
      all_goals norm_num
    rw [h5]
    all_goals norm_num
  have h6 : ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 5 + 3 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) := by
    have h8 : ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 + ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 + 3 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ((3 : ℝ) ^ (1 / 3 : ℝ))) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) := by
      ring_nf
      <;> simp [pow_two, mul_add, add_mul, mul_assoc]
      <;> ring_nf
    rw [h8]
    rw [h2, h3]
    <;> ring_nf
    all_goals nlinarith
  have h3ab : ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))) ^ 3 = 6 := by
    calc
      ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ)) ) ^ 3
          = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 * ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by ring
      _ = 2 * 3 := by rw [h2, h3]
      _ = (6 : ℝ) := by norm_num
  have h7 : ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 9 - 15 * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 6 - 87 * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 - 125 = 0 := by
    have h8 : ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 5 + 3 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) := h6
    have h9 : ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 - 5 = 3 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) := by linarith
    have h10 : (((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 - 5) ^ 3 = 162 * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [h9]
      have h11 : (3 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ) ^ 3 = 27 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ)) ) ^ 3 * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
        ring_nf
        <;> simp [mul_pow, pow_mul, pow_two]
        <;> ring_nf
      rw [h11]
      rw [h3ab]
      all_goals nlinarith
    have h12 : (((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 - 5) ^ 3 - 162 * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 0 := by linarith [h10]
    nlinarith [sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) - (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ))), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ), h2, h3, h6]
  exact_mod_cast h7
  all_goals nlinarith [sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) - (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ((3 : ℝ) ^ (1 / 3 : ℝ)) ), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ( (3 : ℝ) ^ (1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ))), h2, h3, h6]
  all_goals nlinarith [sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) - (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ((3 : ℝ) ^ (1 / 3 : ℝ)) ), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ((3 : ℝ) ^ (1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) + (3 : ℝ) ^ (1 / 3 : ℝ)) ), h2, h3, h6]
  all_goals norm_num
  all_goals nlinarith
  all_goals ring_nf <;> simp [Real.rpow_pos_of_pos, mul_pos, sq_nonneg]
  all_goals norm_num
  all_goals nlinarith
  all_goals tauto
  all_goals norm_num
  all_goals linarith [hx, h1, h2, h3, h6]