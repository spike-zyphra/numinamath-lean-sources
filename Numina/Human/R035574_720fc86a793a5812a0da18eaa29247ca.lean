import Mathlib

/- The value of x that satisfies log_(2^x) (3^20) = log_(2^(x + 3)) (3^2020) can be written
as m/n, where m and n are relatively prime positive integers. Find m + n. -/
theorem algebra_98311 {m n : ℕ} {x : ℝ} (hx : x > 0)
(h: Real.logb (2^x) (3^20) = Real.logb (2^(x + 3)) (3^2020))
(h2: m > 0 ∧ n > 0 ∧ m.Coprime n ∧ x = m / n)
: m + n = 103 := by
  -- let n = the value in the given equation
  have : ∃ n':ℝ, n' = Real.logb (2^x) (3^20) := by use Real.logb (2^x) (3^20)
  obtain ⟨n', hn⟩ := this
  -- remove log
  have hn2 := Eq.symm hn
  rw [Real.logb_eq_iff_rpow_eq (by apply Real.rpow_pos_of_pos; norm_num) (by
    have :=Real.one_lt_rpow (x:=2) (z:=x) (by norm_num) (by linarith)
    linarith) (by norm_num)] at hn2
  have hn3 := Eq.symm hn
  rw [h, Real.logb_eq_iff_rpow_eq (by apply Real.rpow_pos_of_pos; norm_num) (by
    have :=Real.one_lt_rpow (x:=2) (z:=x+3) (by norm_num) (by linarith)
    linarith) (by norm_num)] at hn3
  -- simplify second equation
  conv_lhs at hn3 =>
    calc ((2:ℝ) ^ (x + 3)) ^ n'
    _ = 2 ^ (x * n' + 3 * n') := by rw [← Real.rpow_mul (by norm_num)]; ring_nf
    _ = 2 ^ (x * n') * 2^ (3 * n') := by rw [Real.rpow_add (by norm_num)]
    _ = 2 ^ (x * n') * (2 ^ 3) ^ n' := by rw [Real.rpow_mul (y:=3) (by norm_num)]; ring_nf
    _ = 2 ^ (x * n') * 8 ^ n' := by norm_num
    _ = (2 ^ x) ^ n' * 8 ^ n' := by rw [Real.rpow_mul (by norm_num)]
  -- we can now substitute the first equation into the second one
  rw [hn2] at hn3
  -- simplify
  apply congr_arg (fun x => (3^(-20:ℝ) * x)^(1/100:ℝ)) at hn3
  conv_lhs at hn3 =>
    calc ((3:ℝ) ^ (-20:ℝ) * (3 ^ 20 * 8 ^ n')) ^ (1 / 100:ℝ)
    _ = (3 ^ (-20:ℝ) * 3 ^ (20:ℝ) * 8 ^ n') ^ (1 / 100:ℝ) := by ring_nf
    _ = (3 ^ ((-20:ℝ)+(20:ℝ)) * 8 ^ n') ^ (1 / 100:ℝ) := by rw [Real.rpow_add (by norm_num)]
    _ = (8 ^ n') ^ (1 / 100:ℝ) := by norm_num
    _ = 8 ^ (n' * (1 / 100:ℝ)) := by rw [Real.rpow_mul (by norm_num)]
    _ = 8 ^ ((1 / 100:ℝ) * n') := by ring_nf
    _ = (8 ^ (1 / 100:ℝ)) ^ n' := by rw [Real.rpow_mul (by norm_num)]

  conv_rhs at hn3 =>
    calc ((3:ℝ) ^ (-20:ℝ) * (3:ℝ) ^ 2020) ^ (1 / 100:ℝ)
    _ = ((3:ℝ) ^ (-20:ℝ) * (3:ℝ) ^ (2020:ℝ)) ^ (1 / 100:ℝ) := by ring_nf
    _ = ((3:ℝ) ^ ((-20:ℝ)+ (2020:ℝ))) ^ (1 / 100:ℝ) := by rw [Real.rpow_add (by norm_num)]
    _ = ((3:ℝ) ^ (2000:ℝ)) ^ (1 / 100:ℝ) := by norm_num
    _ = (3 ^ (2000 * (1 / 100:ℝ))) := by rw [Real.rpow_mul (by norm_num)]
    _ = 3 ^ 20 := by norm_num

  -- we can rw with first equation
  rw [← hn2] at hn3
  -- we cancel out the ^n term
  apply congr_arg (fun x=> x^(1/n')) at hn3
  rw [← Real.rpow_mul (by apply Real.rpow_nonneg (by norm_num)), ← Real.rpow_mul (z:=1/n') (by apply Real.rpow_nonneg (by norm_num))] at hn3
  ring_nf at hn3; rw [mul_inv_cancel₀ (by
    rw [hn]; apply Real.logb_ne_zero_of_pos_of_ne_one (Real.one_lt_rpow (x:=2) (z:=x) (by norm_num) (by linarith)) (by norm_num) (by norm_num)), Real.rpow_one, Real.rpow_one] at hn3
  -- we can take log_2 of both sides to obtain x
  apply congr_arg (fun x => Real.logb 2 x) at hn3
  conv_rhs at hn3 => rw [Real.logb_rpow (by norm_num) (by norm_num)]
  conv_lhs at hn3 =>
    calc Real.logb 2 (8 ^ (1 / 100:ℝ))
    _ = Real.logb 2 ((2^3) ^ (1 / 100:ℝ)) := by norm_num
    _ = Real.logb 2 (2 ^ (3 * (1 / 100:ℝ))) := by rw [Real.rpow_mul (by norm_num)]; ring_nf
    _ = 3 * (1 / 100:ℝ) := by rw [Real.logb_rpow (by norm_num) (by norm_num)]
    _ = 3 / 100 := by norm_num
  -- now we are done, just need to deal with the fraction
  obtain ⟨hm, hn, hmn, hx⟩ := h2
  linarith [@Rat.div_int_inj m n 3 100 (by simpa) (by norm_num) (by simpa) (by norm_num) (by rify; linarith)]