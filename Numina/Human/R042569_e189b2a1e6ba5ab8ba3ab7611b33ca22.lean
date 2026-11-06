import Mathlib

/- Let x, y and z be positive real numbers that satisfy
2 log_x (2y) = 2 log_(2x) (4z) = log_(2x^4) (8yz) ≠ 0.
The value of x * y^5 * z can be expressed in the form 1/2^(p/q), where p and q
are relatively prime positive integers. Find p + q. -/

theorem algebra_95229 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(h : 2 * Real.logb x (2 * y) = 2 * Real.logb (2 * x) (4 * z)) (h' : 2 * Real.logb (2 * x) (4 * z) = Real.logb (2 * x ^ 4) (8 * y * z))
(h'' : Real.logb (2 * x ^ 4) (8 * y * z) ≠ 0) :
∃ p q : ℕ, p > 0 ∧ q > 0 ∧ p.Coprime q ∧ (x * y ^ 5 * z) = 1 / 2 ^ (p / q:ℝ) := by
  -- let r be the common value of the three logarithms
  let q: (∃ r:ℝ, r = 2 * Real.logb x (2*y)) := by
    use 2*Real.logb x (2*y)
  obtain ⟨r, rdef⟩ := q
  -- show r cannot be 0
  have rpos: r ≠ 0 := by intro hr; apply h''; linarith
  -- get rid of logarithms
  have h1: x^(r/2) = 2*y := by
    apply congr_arg (fun x=> 0.5 * x) at rdef
    ring_nf at rdef;
    have rdef := Eq.symm rdef;
    rw [Real.logb_eq_iff_rpow_eq (by linarith) (by intro x1; rw [x1, Real.logb_one_left] at rdef; apply rpos; linarith; ) (by linarith)] at rdef
    rw [mul_comm, ← rdef]
    ring_nf
  have h2: (2*x)^(r/2) = 4*z := by
    rw [h] at rdef
    apply congr_arg (fun x=> 0.5 * x) at rdef
    ring_nf at rdef
    have rdef := Eq.symm rdef;
    rw [Real.logb_eq_iff_rpow_eq (by linarith) (by intro x1; rw [x1, Real.logb_one_left] at rdef; apply rpos; linarith) (by linarith)] at rdef
    rw [mul_comm 4, ← rdef]
    ring_nf
  have h3: (2*x^4)^r = 8*y*z := by
    rw [h, h'] at rdef
    have rdef := Eq.symm rdef
    rw [Real.logb_eq_iff_rpow_eq (by refine mul_pos (by norm_num) ?_; norm_cast; rw [pow_succ, pow_succ, pow_succ, pow_one]; exact mul_pos (mul_pos (mul_pos hx hx) hx) hx) (by intro x1; rw [x1, Real.logb_one_left] at rdef; apply rpos; linarith) (by refine mul_pos ?_ hz; linarith)] at rdef
    assumption

  -- multiplying h1 and h2 we get h3. So left hand sides can be matched
  have h4: (2*y) * (4*z) = 8*y*z := by ring_nf
  rw [← h1, ← h2, ← h3, ← Real.mul_rpow (by linarith) (by linarith), Real.rpow_div_two_eq_sqrt, Real.rpow_left_inj (by simp) (by simp; rw [pow_succ, pow_succ, pow_succ, pow_one]; have:= mul_pos (mul_pos (mul_pos hx hx) hx) hx; linarith) (by assumption)] at h4
  ring_nf at h4; norm_num at h4; rw [Real.sqrt_sq (by linarith)] at h4
  -- shuffle terms to solve for x
  apply congr_arg (fun t=> x⁻¹ * t / 2) at h4
  ring_nf at h4; rw [mul_inv_cancel₀ (by linarith), one_mul, inv_eq_one_div, ← mul_div_assoc, mul_one, ← mul_div_assoc, mul_one] at h4;
  have:4=3+1 := by norm_num;
  rw [this, pow_succ, mul_div_assoc, div_self (by linarith), mul_one] at h4;
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add] at h4; norm_num at h4;
  have hx:=
    calc x
    _ = (x^(3:ℝ))^(1/3:ℝ) := by rw [← Real.rpow_mul (by linarith)]; norm_num
    _ = (x^3)^(1/3:ℝ) := by norm_cast;
    _ = (2^(-1/2:ℝ))^(1/3:ℝ) := by rw [← h4]; ring_nf
    _ = 2^(-1/6:ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  -- now we can work towards computing x * y^5 * z
  have xy5z :=
    calc x * y^5 * z
    _ = (2^(-1/6:ℝ)) * y^5 * z := by rw [hx]
    _ = 2^(-1/6:ℝ) * (2*y)^5/(2^5) * (4*z)/4 := by ring_nf
    _ = 2^(-1/6:ℝ) * (x^(r/2))^5/(2^5) * (2*x)^(r/2)/4 := by rw [h1, h2]
    _ = (2:ℝ)^(-1/6:ℝ)*(2:ℝ)^(-7:ℝ) * (x^(r/2))^(5:ℝ) * (2*x)^(r/2) := by ring_nf; norm_cast; ring_nf;
    _ = (2:ℝ)^((-1/6:ℝ)+(-7:ℝ)) * (x^(5*r/2)) * 2^(r/2) * x^(r/2) := by rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul (by linarith), Real.mul_rpow (by norm_num) (by linarith)]; ring_nf
    _ = (2:ℝ)^(-43/6:ℝ) * ((x^(5*r/2)) * x^(r/2)) * 2^(r/2) := by ring_nf;
    _ = (2:ℝ)^(-43/6:ℝ) * x^(3*r) * 2^(r/2) := by rw [← Real.rpow_add (by assumption)]; ring_nf
    _ = (2:ℝ)^(-43/6:ℝ) * (2^(-1/6:ℝ))^(3*r) * 2^(r/2) := by rw [hx]
    _ = (2:ℝ)^(-43/6:ℝ) := by rw [← Real.rpow_mul, ← Real.rpow_add, ← Real.rpow_add]; ring_nf; all_goals {norm_num}
  -- now just the buerocracy to get things done
  rw [xy5z]
  use 43, 6
  norm_num
  rw [← Real.rpow_neg_one, ← Real.rpow_mul];
  norm_num
  norm_num
  norm_num
  exact mul_nonneg (a:=x) (by linarith) (by linarith)