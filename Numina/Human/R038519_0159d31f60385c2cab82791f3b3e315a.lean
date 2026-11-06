import Mathlib

/- Task 11.6. (14 points)

Real numbers $a$ and $b$ are such that $\left(a+\sqrt{1+a^{2}}\right)\left(b+\sqrt{1+b^{2}}\right)=1$. Find the sum $a+b$.

# -/
theorem algebra_238191 {a b : ℝ} (h : (a + Real.sqrt (1 + a ^ 2)) * (b + Real.sqrt (1 + b ^ 2)) = 1) :
    a + b = 0 := by
    -- we first show that neither part of the product can be zero
    have hapos: a + Real.sqrt (1 + a ^ 2) ≠ 0 := by
      intro h'; rw [h'] at h; linarith
    have hbpos: b + Real.sqrt (1 + b ^ 2) ≠ 0 := by
      intro h'; rw [h'] at h; linarith
    -- we can now divide to get two new equations
    have hb := congr_arg (fun x => (a + Real.sqrt (1 + a ^ 2))⁻¹ * x) h
    have ha := congr_arg (fun x => x * (b + Real.sqrt (1 + b ^ 2))⁻¹) h
    simp at ha hb
    rw [mul_inv_cancel_right₀ (by assumption)] at ha
    rw [← mul_assoc, mul_comm (a + √(1 + a ^ 2))⁻¹, mul_inv_cancel₀ (by assumption), one_mul] at hb
    -- rationalize the equation
    conv_rhs at ha =>
      calc _
      _ = 1/(b + √(1 + b ^ 2)) := by ring_nf
      _ = 1/(b + √(1 + b ^ 2)) * ((b - √(1 + b ^ 2))/ (b - √(1 + b ^ 2))) := by rw [div_self (by
        suffices b < √(1+b^2) by linarith
        apply Real.lt_sqrt_of_sq_lt
        linarith
      ), mul_one]
      _ = (b - √(1 + b ^ 2))/(b + √(1 + b ^ 2))/ (b - √(1 + b ^ 2)) := by ring_nf
      _ = (b - √(1 + b ^ 2))/((b + √(1 + b ^ 2)) * (b - √(1 + b ^ 2))) := by rw [div_div]
      _ = (b - √(1 + b ^ 2))/(b^2 - (√(1 + b ^ 2))^2) := by ring_nf
      _ = (b - √(1 + b ^ 2))/((b^2 - (1 + b ^ 2))) := by rw [Real.sq_sqrt (by nlinarith)]
      _ = -b + √(1 + b ^ 2) := by ring_nf
    conv_rhs at hb =>
      calc _
      _ = 1/(a + √(1 + a ^ 2)) := by ring_nf
      _ = 1/(a + √(1 + a ^ 2)) * ((a - √(1 + a ^ 2))/ (a - √(1 + a ^ 2))) := by rw [div_self (by
        suffices a < √(1+a^2) by linarith
        apply Real.lt_sqrt_of_sq_lt
        linarith
      ), mul_one]
      _ = (a - √(1 + a ^ 2))/(a + √(1 + a ^ 2))/ (a - √(1 + a ^ 2)) := by ring_nf
      _ = (a - √(1 + a ^ 2))/((a + √(1 + a ^ 2)) * (a - √(1 + a ^ 2))) := by rw [div_div]
      _ = (a - √(1 + a ^ 2))/(a^2 - (√(1 + a ^ 2))^2) := by ring_nf
      _ = (a - √(1 + a ^ 2))/((a^2 - (1 + a ^ 2))) := by rw [Real.sq_sqrt (by nlinarith)]
      _ = -a + √(1 + a ^ 2) := by ring_nf
    -- we can add the two equations together
    have hsum : a + √(1 + a ^ 2) + b + √(1 + b ^ 2) = -b + √(1 + b ^ 2) + -a + √(1 + a ^ 2) := by linarith
    -- we can now cancel the square roots
    apply congr_arg (fun x => x - √(1 + a ^ 2) - √(1 + b ^ 2)) at hsum
    ring_nf at hsum;
    -- the conclusion follows
    linarith