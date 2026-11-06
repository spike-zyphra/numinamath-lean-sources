import Mathlib

/- Prove that if


$$

p+q+r=1

$$


and


$$

\frac{1}{p}+\frac{1}{q}+\frac{1}{r}=0

$$


then


$$

a^{2}+b^{2}+c^{2}=(p a+q b+r c)^{2}+(q a+r b+p c)^{2}+(r a+p b+q c)^{2}

$$
 -/
theorem algebra_159262 {p q r a b c : ℝ} (h₀ : p + q + r = 1) (h₁ : 1 / p + 1 / q + 1 / r = 0) :
    a ^ 2 + b ^ 2 + c ^ 2 = (p * a + q * b + r * c) ^ 2 +
      (q * a + r * b + p * c) ^ 2 + (r * a + p * b + q * c) ^ 2
  := by
    -- Group RHS into similar terms
    convert_to a ^ 2 + b ^ 2 + c ^ 2
      = a ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2)
      + b ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2)
      + c ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2)
      + 2 * a * b * (p * q + q * r + r * p)
      + 2 * b * c * (p * q + q * r + r * p)
      + 2 * c * a * (p * q + q * r + r * p)
    · ring

    -- sum of pairwise products is zero: p * q + q * r + r * p = 0
    have mul_eq : p * q + q * r + r * p = 0 := by
      -- none of p q r is zero
      -- p is not zero
      by_cases hp : p = 0
      · subst hp
        by_cases hq : q = 0
        · subst hq
          linarith
        · by_cases hr : r = 0
          · subst hr
            linarith
          · apply_fun (· * (q * r)) at h₁
            ring_nf at h₁
            nth_rw 2 [mul_assoc] at h₁
            rw [(mul_inv_eq_one₀ hq).mpr rfl,
              (mul_inv_eq_one₀ hr).mpr rfl] at h₁
            linarith
      -- q is not zero
      by_cases hq : q = 0
      · subst hq
        by_cases hr : r = 0
        · subst hr
          linarith
        · apply_fun (· * (p * r)) at h₁
          ring_nf at h₁
          nth_rw 2 [mul_assoc] at h₁
          rw [(mul_inv_eq_one₀ hp).mpr rfl,
            (mul_inv_eq_one₀ hr).mpr rfl] at h₁
          linarith
      -- r is not zero
      by_cases hr : r = 0
      · subst hr
        apply_fun (· * (p * q)) at h₁
        ring_nf at h₁
        nth_rw 2 [mul_assoc] at h₁
        rw [(mul_inv_eq_one₀ hp).mpr rfl,
          (mul_inv_eq_one₀ hq).mpr rfl] at h₁
        linarith

      -- non-zero numbers multiplied with their inverse is equal to 1
      have p_mul_inv : p * p⁻¹ = 1
        := CommGroupWithZero.mul_inv_cancel p hp
      have q_mul_inv : q * q⁻¹ = 1
        := CommGroupWithZero.mul_inv_cancel q hq
      have r_mul_inv : r * r⁻¹ = 1
        := CommGroupWithZero.mul_inv_cancel r hr

      -- multiply both sides of h₁ by p * q * r
      apply_fun (· * (p * q * r)) at h₁
      ring_nf at h₁
      -- reorder to match h₁
      convert_to q * r + p * r + p * q = 0
      · ring
      -- equality of terms
      convert h₁ using 2
      congr
      · rw [p_mul_inv, one_mul]
      · rw [mul_assoc, q_mul_inv, mul_one]
      · convert_to p * q = p * q * (r * r⁻¹)
        · ring
        rw [r_mul_inv, mul_one]

    -- square h₀
    apply_fun (· ^ 2) at h₀
    -- expand terms and group (p * q + q * r + r * p)
    convert_to p ^ 2 + q ^ 2 + r ^ 2 + 2 * (p * q + q * r + r * p) = 1 at h₀
    · ring
    · ring
    -- simplify h₀ using p * q + q * r + r * p = 0
    rw [mul_eq, mul_zero, add_zero] at h₀

    -- Simplify RHS using
    -- p * q + q * r + r * p = 0 and p ^ 2 + q ^ 2 + r ^ 2 = 1
    -- then both sides are clearly equal
    simp only [mul_eq, h₀, mul_zero, add_zero, mul_one]