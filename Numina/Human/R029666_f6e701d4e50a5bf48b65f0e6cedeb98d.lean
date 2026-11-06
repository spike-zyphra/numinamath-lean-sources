import Mathlib
set_option maxHeartbeats 200000000
/- Task 3. Let $a, b$ and $c$ be positive real numbers satisfying $a+b+c \geq a b c$. Prove that


$$

a^{2}+b^{2}+c^{2} \geq \sqrt{3} a b c .

$$
 -/
theorem inequalities_168319 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ a + b + c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by
    -- let's first show a^2 + b^2 + c^2 ≥ a*b + b*c + c*a
    have h0: ∀a b c:ℝ, 0 < a → 0 < b → 0 < c → a*b + b*c + c*a ≤ a^2 + b^2 + c^2 := by
      intros a b c ha hb hc
      suffices 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a) by linarith
      conv_rhs =>
        calc _
        _ = (a-b)^2/2 + (b-c)^2/2 + (c-a)^2/2 := by ring_nf
      nlinarith
    -- next we show that 3*(a^2+b^2+c^2) ≥ (a+b+c)^2
    have h1: ∀a b c:ℝ, 0 < a → 0 < b → 0 < c → (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
      intros a b c ha hb hc
      suffices 3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2 ≥ 0 by linarith
      calc _
      _ = 2*(a^2+b^2+c^2)-2*a*b-2*b*c-2*c*a := by ring_nf
      _ ≥ 0 := by linarith [h0 a b c ha hb hc]
    -- next we use AMGM on a, b, c
    have h2: 3*(a*b*c)^(1/3:ℝ)≤ a+b+c := by
      have q:= Real.geom_mean_le_arith_mean3_weighted (w₁:=1/3) (w₂:=1/3) (w₃:=1/3) (p₁:=a) (p₂:=b) (p₃:=c) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
      conv_lhs at q =>
       calc _
       _ =  (a*b*c)^(1/3:ℝ) := by rw [Real.mul_rpow (by nlinarith) (by nlinarith), Real.mul_rpow (by nlinarith) (by nlinarith)];
      apply (mul_le_mul_right (a:=3⁻¹ ) (by norm_num)).mp
      ring_nf; linarith
    -- we can now obtain two inequalities for a^2 + b^2 + c^2
    have h3:=
      calc a^2+b^2+c^2
      _ ≥ (a+b+c)^2/3 := by linarith [h1 a b c ha hb hc]
      _ ≥ 3*(a*b*c)^(2/3:ℝ) := by
        simp
        apply (mul_le_mul_left (a:=3) (by norm_num)).mp
        conv_rhs =>
          calc _
          _ = (a + b + c) ^ (2:ℝ) := by rw [mul_div, mul_comm, mul_div_assoc, div_self (by norm_num), mul_one]; norm_cast
        conv_lhs =>
          calc _
          _ = 9 * (a * b * c) ^ (2 / 3:ℝ) := by ring_nf
          _ = 9 * ((a * b * c) ^ (1/3:ℝ))^ (2:ℝ) := by rw [div_eq_mul_inv, mul_comm 2, Real.rpow_mul (by apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith)]; ring_nf
          _ = (3 * (a*b*c)^(1/3:ℝ))^(2:ℝ) := by rw [Real.mul_rpow (z:=2) (by nlinarith) (by apply Real.rpow_nonneg; apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith)]; ring_nf
        exact Real.rpow_le_rpow (by simp; apply Real.rpow_nonneg; apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith) h2 (by norm_num)

    have h4:=
      calc a^2+b^2+c^2
      _ ≥ (a+b+c)^2/3 := by linarith [h1 a b c ha hb hc]
      _ ≥ (a*b*c)^2/3 := by
        simp
        apply (mul_le_mul_right (a:=3) (by norm_num)).mp; norm_num
        apply pow_le_pow_left₀ (by apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith); assumption
    -- the appropriate mixture completes the result
    calc _
    _ = (a ^ 2 + b ^ 2 + c ^ 2)^(3/4:ℝ) * (a^2 + b^2 + c^2)^(1/4:ℝ) := by rw [← Real.rpow_add (by nlinarith)]; norm_num
    _ ≥ (3*(a*b*c)^(2/3:ℝ))^(3/4:ℝ) * (1/3 * (a*b*c)^2)^(1/4:ℝ) := by
      apply mul_le_mul
      · apply Real.rpow_le_rpow
        simp
        apply Real.rpow_nonneg
        apply mul_nonneg
        apply mul_nonneg
        nlinarith
        nlinarith
        nlinarith
        nlinarith
        norm_num
      · apply Real.rpow_le_rpow
        simp
        nlinarith
        linarith
        norm_num
      · apply Real.rpow_nonneg
        nlinarith
      · apply Real.rpow_nonneg
        nlinarith
    _ = (3*(a*b*c)^(2/3:ℝ))^(3/4:ℝ) * (1/3 * (a*b*c)^(2:ℝ))^(1/4:ℝ) := by norm_cast
    _ = 3^(3/4:ℝ)*(a*b*c)^(1/2:ℝ) * (1/3)^(1/4:ℝ) * (a*b*c)^(1/2:ℝ) := by rw [Real.mul_rpow (by norm_num) (by apply Real.rpow_nonneg; apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith), ← Real.rpow_mul (by apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith), Real.mul_rpow (z:=1/4) (by norm_num) (by apply Real.rpow_nonneg; apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith), ← Real.rpow_mul (by apply mul_nonneg; apply mul_nonneg; nlinarith; nlinarith; nlinarith)]; ring_nf
    _ = 3^(3/4:ℝ)*(1/3)^(1/4:ℝ)*(a*b*c)^(1/2:ℝ)*(a*b*c)^(1/2:ℝ) := by ring_nf
    _ = 3^(1/2:ℝ)*a*b*c := by rw [Real.div_rpow (by norm_num) (by norm_num), div_eq_mul_inv (b:=3^(1/4:ℝ)), ← Real.rpow_neg (by norm_num)]; simp; rw [← Real.rpow_add (by norm_num), div_eq_mul_inv, mul_assoc, ← Real.rpow_add (by apply mul_pos; apply mul_pos; assumption; assumption; assumption)]; ring_nf; simp; ring_nf
    _ = √3 * a * b * c := by rw [Real.sqrt_eq_rpow]