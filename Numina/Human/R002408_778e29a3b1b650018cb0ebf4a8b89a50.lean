import Mathlib

/- Let x = 4 / ((√5 + 1)(5^(1/4) + 1)(5^(1/8) + 1)(5^(1/16) + 1)). Find (x + 1)^48. -/
theorem algebra_92957 {x : ℝ}
(hx : x = 4 / ((Real.sqrt 5 + 1) * (5 ^ ((1 : ℝ) / 4) + 1) * (5 ^ ((1 : ℝ) / 8) + 1) * (5 ^ ((1 : ℝ) / 16) + 1))) :
(x + 1) ^ 48 = 125 := by
  -- first, rewrite sqrt as ^
  rw [Real.sqrt_eq_rpow] at hx
  -- since (5^a-1)*(5^a+1)=5^(2a)-1 we multiply/divide by (5^(1/16) - 1) and telescope
  have :=
    calc x
    _ = 4 / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 8:ℝ) + 1) * (5 ^ (1 / 16:ℝ) + 1)) := by rw [hx]
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 8:ℝ) + 1) * (5 ^ (1 / 16:ℝ) + 1) * (5^(1/16:ℝ) - 1)) := by
      rw [mul_div_assoc, mul_comm _ (5 ^ (1 / 16) - 1), ← div_div (5 ^ (1 / 16) - 1), div_self (by intro h; apply congr_arg (fun x=>(x+1)^(16:ℝ)) at h; simp at h)]; ring_nf
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 8:ℝ) + 1) * (5 ^ (1 / 16:ℝ)*5^(1/16:ℝ) - 1)) := by ring_nf
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 8:ℝ) + 1) * (5 ^ (1 / 8:ℝ) - 1)) := by rw [← Real.rpow_add (by norm_num)]; norm_num
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 8:ℝ)* 5 ^ (1 / 8:ℝ) - 1)) := by ring_nf
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) + 1) * (5 ^ (1 / 4:ℝ) - 1)) := by rw [← Real.rpow_add (by norm_num)]; norm_num
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 4:ℝ) * 5 ^ (1 / 4:ℝ) - 1)) := by ring_nf
    _ = 4 * (5^(1/16:ℝ) - 1) / ((5 ^ (1 / 2:ℝ) + 1) * (5 ^ (1 / 2:ℝ) - 1)) := by rw [← Real.rpow_add (by norm_num)]; norm_num
    _ = 4 * (5^(1/16:ℝ) - 1) / (5 ^ (1 / 2:ℝ) * 5 ^ (1 / 2:ℝ) - 1) := by ring_nf
    _ = 4 * (5^(1/16:ℝ) - 1) / (5 - 1) := by rw [← Real.rpow_add (by norm_num)]; norm_num
    _ = 5^(1/16:ℝ) - 1  := by norm_num
  rw [this]
  -- easy algebra to finish
  calc ((5:ℝ) ^ (1 / 16:ℝ) - 1 + 1) ^ 48
  _ = (5 ^ (1 / 16:ℝ)) ^ (48:ℝ) := by norm_num; norm_cast
  _ = 5 ^ (48 / 16:ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  _ = 5 ^ 3 := by norm_num
  _ = 125 := by norm_num