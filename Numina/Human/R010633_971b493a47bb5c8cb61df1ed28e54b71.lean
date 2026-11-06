import Mathlib

open Real

/- 7.280. $\left\{\begin{array}{l}2\left(\log _{1 / y} x-2 \log _{x^{2}} y\right)+5=0, \\ x y^{2}=32 .\end{array}\right.$ -/
theorem algebra_167976 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx': x ≠ 1) (hy': y ≠ 1)
    (h1 : 2 * (logb (1 / y) x - 2 * logb (x ^ 2) y) + 5 = 0) (h2 : x * y ^ 2 = 32) :
    (x = 2 ∧ y = 4) ∨ (x = 4 * sqrt 2 ∧ y = 2 * 2 ^ ((1 : ℝ) / 4)) := by
  -- in first equation we change to base 2
  have := Real.mul_logb (a:=2) (b:=1/y) (c:=x) (by simp; linarith) (by simp; assumption) (by simp; intro h; apply congr_arg (fun x => x⁻¹) at h; simp at h; norm_num at h; linarith)
  apply congr_arg (fun x => x / (logb 2 (1 / y))) at this
  rw [mul_comm, mul_div_assoc, div_self (by simp; exact ⟨by norm_num, ⟨by linarith, ⟨by assumption, by linarith⟩⟩⟩), mul_one] at this
  rw [this] at h1

  have := Real.mul_logb (a:=2) (b:=x^2) (c:=y) (by simp; linarith) (by simp;exact ⟨by assumption, by linarith⟩) (by have :=sq_nonneg x; linarith)
  apply congr_arg (fun x' => x' / (logb 2 (x^2))) at this
  rw [mul_comm, mul_div_assoc, div_self (by simp; exact ⟨by norm_num, ⟨by linarith, ⟨⟨by assumption, by linarith⟩, by have :=sq_nonneg x; linarith⟩⟩⟩), mul_one] at this
  rw [this] at h1

  -- we take logb 2 of both sides of the second equation
  have h2bak := h2
  apply congr_arg (fun x=> logb 2 x ) at h2
  conv_lhs at h2 =>
    calc _
    _ = logb 2 x + logb 2 (y^2) := by rw [logb_mul (by linarith) (by simp; linarith)]
    _ = logb 2 x + 2 * logb 2 y := by rw [logb_pow]; norm_cast
  conv_rhs at h2 =>
    calc _
    _ = logb 2 (2^5) := by norm_num
    _ = 5 := by rw [logb_pow]; norm_cast; simp
  have h2':logb 2 x = 5 - 2 * logb 2 y := by linarith
  -- substitute into the first equation
  conv_lhs at h1 =>
    calc _
    _ = 2 * (-(logb 2 x / logb 2 y) - 2 * (logb 2 y / (2 * logb 2 x))) + 5 := by rw [one_div, logb_inv, logb_pow]; ring_nf
    _ = 2 * (-((5 - 2 * logb 2 y)/ logb 2 y) - 2 * (logb 2 y / (2 * (5 - 2 * logb 2 y)))) + 5 := by rw [h2']
  -- multiply both sides to get rid of denominators
  apply congr_arg (fun x => x * logb 2 y * (5 - 2 * logb 2 y)) at h1
  rw [zero_mul, zero_mul] at h1

  conv_lhs at h1 =>
    calc _
    _ = -2 * (((5 - 2 * logb 2 y) / logb 2 y) + 2 * (logb 2 y / (2 * (5 - 2 * logb 2 y)))) * logb 2 y *(5 - 2 * logb 2 y) + 5 * logb 2 y *(5 - 2 * logb 2 y) := by ring_nf
    _ = ((5 - 2 * logb 2 y) * (logb 2 y / logb 2 y)) * (-2) * (5 - 2 * logb 2 y) + 2 * (logb 2 y * ((5 - 2 * logb 2 y) / (2 * (5 - 2 * logb 2 y)))) * (-2) * logb 2 y+ 5 * logb 2 y *(5 - 2 * logb 2 y) := by ring_nf
    _ = ((5 - 2 * logb 2 y)) * (-2) * (5 - 2 * logb 2 y) + 2 * (logb 2 y * ((5 - 2 * logb 2 y) / 2 / (5 - 2 * logb 2 y))) * (-2) * logb 2 y+ 5 * logb 2 y *(5 - 2 * logb 2 y) := by rw [div_div, div_self (by simp; exact ⟨by norm_num, ⟨by linarith, ⟨by assumption, by linarith⟩⟩⟩), mul_one];
    _ = ((5 - 2 * logb 2 y)) * (-2) * (5 - 2 * logb 2 y) + 2 * (logb 2 y * ((5 - 2 * logb 2 y) / (5 - 2 * logb 2 y))) * (-1) * logb 2 y + 5 * logb 2 y *(5 - 2 * logb 2 y) := by ring_nf
    _ = ((5 - 2 * logb 2 y)) * (-2) * (5 - 2 * logb 2 y) + 2 * logb 2 y * (-1) * logb 2 y + 5 * logb 2 y *(5 - 2 * logb 2 y) := by rw [div_self (by
      intro h
      apply congr_arg (fun x => (-5+x)/ -2) at h
      ring_nf at h
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hy] at h
      rw [← h] at h2bak
      apply hx'
      conv_lhs at h2bak =>
        calc _
        _ = x * ((2:ℝ) ^ (5 / 2:ℝ)) ^ (2:ℝ) := by norm_cast
        _ = x * ((2:ℝ) ^ (5 / 2 * 2:ℝ)) := by rw [rpow_mul (by norm_num)];
        _ = x * ((2:ℝ) ^ (5:ℝ)) := by norm_num
        _ = x * 32 := by norm_num
      simp at h2bak; assumption
    ), mul_one]
    _ = -50 + (logb 2 y * 65 - logb 2 y ^ 2 * 20) := by ring_nf
  -- we solve a quadratic in logb 2 y
  have sol := (quadratic_eq_zero_iff (a:=(-20:ℝ)) (b:=(65:ℝ)) (c:=(-50:ℝ)) (by norm_num) (s:=15) (by unfold discrim; norm_num) (logb 2 y)).mp
  ring_nf at h1 sol
  specialize sol h1
  -- quadratic has two solutions
  cases' sol with sol sol
  · rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hy] at sol
    right
    constructor
    · rw [← sol] at h2bak
      apply congr_arg (fun x=> x / ((2 ^ (5 / 4:ℝ)) ^ 2)) at h2bak
      rw [mul_div_assoc, div_self (by norm_num), mul_one] at h2bak
      rw [h2bak]
      calc 32 / ((2:ℝ) ^ (5 / 4:ℝ)) ^ 2
      _ = 32 / ((2:ℝ) ^ (5 / 4:ℝ)) ^ (2:ℝ) := by norm_num
      _ = 32 / ((2:ℝ) ^ (5 / 2:ℝ)) := by rw [← rpow_mul (by norm_num)]; norm_num
      _ = (2:ℝ)^(5:ℝ) * (2:ℝ) ^ (-5 / 2:ℝ) := by rw [div_eq_mul_inv, ← rpow_neg (by norm_num)]; norm_num
      _ = (2:ℝ) ^ (5 - 5 / 2:ℝ) := by rw [← rpow_add (by norm_num)]; norm_num
      _ = (2:ℝ) ^ (2 + 1/2:ℝ) := by norm_num
      _ = (2:ℝ) ^ 2 * (2:ℝ) ^ (1 / 2:ℝ) := by rw [rpow_add (by norm_num)]; norm_num
      _ = 4 * (2:ℝ) ^ (1 / 2:ℝ) := by norm_num
      _ = 4 * √2 := by apply congr_arg; rw [sqrt_eq_rpow]
    rw [← sol]
    calc (2:ℝ) ^ (5 / 4:ℝ)
    _ = (2:ℝ) ^ (1 + 1 / 4:ℝ) := by norm_num
    _ = 2 * 2 ^ (1 / 4:ℝ) := by rw [rpow_add (by norm_num)]; norm_num
  · rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hy] at sol
    left
    norm_num at sol
    rw [← sol] at h2bak
    norm_num at h2bak
    exact ⟨by linarith, sol.symm⟩