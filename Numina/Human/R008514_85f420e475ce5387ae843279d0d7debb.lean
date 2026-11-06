import Mathlib

open Real

/-
Let $ a, b, c $ be three strictly positive real numbers. Show that

$$
\frac{a^{4}+1}{b^{3}+b^{2}+b}+\frac{b^{4}+1}{c^{3}+c^{2}+c}+\frac{c^{4}+1}{a^{3}+a^{2}+a} \geqslant 2
$$
-/
theorem inequalities_607163
    (a b c : ℝ)
    (h_apos : 0 < a)
    (h_bpos : 0 < b)
    (h_cpos : 0 < c) :
    ((a^4 + 1) / (b^3 + b^2 + b)) + ((b^4 + 1) / (c^3 + c^2 + c)) + ((c^4 + 1) / (a^3 + a^2 + a)) ≥ 2 := by

  -- AM-GM inequality for three nonnegative variables
  have amgm_3 (a b c : ℝ) : 0 ≤ a → 0 ≤ b → 0 ≤ c → 3 * (a * b * c) ^ (1 / 3 : ℝ) ≤ a + b + c := by
    intro ha hb hc
    have t1 : 0 ≤ (1 / 3 : ℝ) := by norm_num
    have := Real.geom_mean_le_arith_mean3_weighted t1 t1 t1 ha hb hc (by norm_num)
    rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (by positivity) hc,
        ← mul_add, ← mul_add] at this
    replace := mul_le_mul_of_nonneg_left this zero_le_three
    rw [one_div, mul_inv_cancel_left₀ three_ne_zero, ← one_div] at this
    exact this

  -- AM-GM inequality for two nonnegative variables
  have amgm_2 (a b : ℝ) : 0 ≤ a → 0 ≤ b → √ (a * b) ≤ 1 / 2 * (a + b) := by
    intro ha hb
    have t1 : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have := Real.geom_mean_le_arith_mean2_weighted t1 t1 ha hb (by norm_num)
    rw [← Real.mul_rpow ha hb, ← mul_add,
        Real.rpow_div_two_eq_sqrt 1 (by positivity), Real.rpow_one] at this
    linarith

  -- We start by applying the AM-GM inequality to the three terms in the statement: $$ \frac{a^{4}+1}{b^{3}+b^{2}+b}+\frac{b^{4}+1}{c^{3}+c^{2}+c}+\frac{c^{4}+1}{a^{3}+a^{2}+a} \geqslant 3 \sqrt[3]{\frac{\left(a^{4}+1\right)\left(b^{4}+1\right)\left(c^{4}+1\right)}{\left(b^{3}+b^{2}+b\right)\left(c^{3}+c^{2}+c\right)\left(a^{3}+a^{2}+a\right)}} $$
  have h1 : ((a^4 + 1) / (b^3 + b^2 + b)) + ((b^4 + 1) / (c^3 + c^2 + c)) + ((c^4 + 1) / (a^3 + a^2 + a)) ≥ 3 * (((a^4 + 1) * (b^4 + 1) * (c^4 + 1)) / ((b^3 + b^2 + b) * (c^3 + c^2 + c) * (a^3 + a^2 + a))) ^ (1 / 3 : ℝ) := by

    -- have {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 ≤ (x^4 + 1) / (y^3 + y^2 + y) := by
    --   positivity

    have := amgm_3
      ((a^4 + 1) / (b^3 + b^2 + b))
      ((b^4 + 1) / (c^3 + c^2 + c))
      ((c^4 + 1) / (a^3 + a^2 + a))
      (by positivity)
      (by positivity)
      (by positivity)

    simp_rw [div_mul_div_comm] at this
    exact ge_iff_le.mpr this

  -- We aim to find a lower bound for the quotients $ \frac{a^{4}+1}{a^{3}+a^{2}+a} $. To do this, we apply AM-GM inequalities:
  -- $$ \begin{aligned} a^{3}+a^{2}+a & \leqslant \frac{1}{2}\left(a^{4}+a^{2}\right)+a^{2}+\frac{1}{2}\left(a^{2}+1\right) = \frac{1}{2}\left(a^{4}+1\right)+2a^{2} \\ & \leqslant \frac{1}{2}\left(a^{4}+1\right)+\left(a^{4}+1\right) = \frac{3}{2}\left(a^{4}+1\right) \end{aligned} $$
  have h2 {x : ℝ} : 0 < x → x ^ 3 + x ^ 2 + x ≤ 3 / 2 * (x ^ 4 + 1) := by --1 / 2 * (x ^ 4 + 1) + 2 * x ^ 2 := by
    intro h
    have t1 : x ^ 3 ≤ 1 / 2 * (x ^ 4 + x ^ 2) := by
      convert amgm_2 (x ^ 4) (x ^ 2) (by positivity) (by positivity)
      rw [← pow_add, show 4 + 2 = 3 * 2 by norm_num, pow_mul, sqrt_sq (by positivity)]

    have t2 : x ≤ 1 / 2 * (x ^ 2 + 1) := by
      convert amgm_2 (x ^ 2) 1 (by positivity) (by positivity)
      field_simp

    have t3 : x ^ 2 ≤ 1 / 2 * (x ^ 4 + 1) := by
      convert amgm_2 (x ^ 4) 1 (by positivity) (by positivity)
      rw [mul_one, show 4 = 2 * 2 by norm_num, pow_mul, sqrt_sq (sq_nonneg x)]

    linarith only [t1, t2, t3]

  -- Thus, $ \frac{a^{4}+1}{a^{3}+a^{2}+a} \geqslant \frac{2}{3} $.
  have h3 {x : ℝ} : 0 < x → (x ^ 4 + 1) / (x ^ 3 + x ^ 2 + x) ≥ 2 / 3 := by
    intro h
    specialize h2 h
    have : 0 ≤ 2 / 3 * (x ^ 3 + x ^ 2 + x)⁻¹ := by positivity
    apply ge_iff_le.mpr
    convert mul_le_mul_of_nonneg_right h2 this using 1
    . rw [mul_comm (2 / 3), mul_inv_cancel_left₀ (by positivity)]
    . ring_nf

  -- so $$ \frac{a^{4}+1}{b^{3}+b^{2}+b}+\frac{b^{4}+1}{c^{3}+c^{2}+c}+\frac{c^{4}+1}{a^{3}+a^{2}+a} \geqslant 3 \sqrt[3]{\left(\frac{2}{3}\right)^{3}} = 2$$
  trans 3 * (((a^4 + 1) / (a^3 + a^2 + a)) * ((b^4 + 1) / (b^3 + b^2 + b)) * ((c^4 + 1) / (c^3 + c^2 + c))) ^ (1 / 3 : ℝ)
  . simp_rw [div_mul_div_comm]
    convert h1 using 4
    ring
  trans 3 * ((2 / 3 : ℝ) ^ 3) ^ (1 / 3 : ℝ)
  . have : (2 / 3 : ℝ) ^ 3 ≤ ((a^4 + 1) / (a^3 + a^2 + a)) * ((b^4 + 1) / (b^3 + b^2 + b)) * ((c^4 + 1) / (c^3 + c^2 + c)) := by
      conv => lhs; simp only [pow_three, ← mul_assoc]
      apply mul_le_mul ?_ ?_ (by norm_num) (by positivity)
      . apply mul_le_mul ?_ ?_ (by norm_num) (by positivity)
        <;> exact ge_iff_le.mp (h3 (by simp_all only))
      exact ge_iff_le.mp (h3 (by simp_all only))
    apply ge_iff_le.mpr
    apply (mul_le_mul_iff_of_pos_left zero_lt_three).mpr
    apply (rpow_le_rpow_iff (by norm_num) (by positivity) (show 0 < (1 / 3 : ℝ) by norm_num)).mpr
    exact this
  . apply ge_of_eq
    have := pow_rpow_inv_natCast (show 0 ≤ (2 / 3 : ℝ) by norm_num) three_ne_zero
    rw [Nat.cast_ofNat] at this
    rw [one_div, this, mul_div_cancel₀ _ three_ne_zero]