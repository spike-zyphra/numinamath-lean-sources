import Mathlib

open Real

/- 1. If $a x^{3}=b y^{3}=c z^{3}$ and $\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=1$, prove that


$$

\sqrt[3]{a x^{2}+b y^{2}+c z^{2}}=\sqrt[3]{a}+\sqrt[3]{b}+\sqrt[3]{c}

$$
 -/
theorem algebra_252161 {a b c x y z : ℝ} (h_apos: a > 0) (h_bpos: b > 0) (h_cpos: c > 0)
  (h_xpos: x > 0) (h_ypos: y > 0) (h_zpos: z > 0)
    (h_ab : a * x^3 = b * y^3) (h_bc : b * y^3 = c * z^3) (h_recip : 1 / x + 1 / y + 1 / z = 1) :
    (a * x^2 + b * y^2 + c * z^2) ^ ((1 : ℝ) / 3) =
    (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) + c ^ ((1 : ℝ) / 3)) := by
  have h_ca: c * z^3 = a * x^3 := by symm; rwa [h_ab]
  -- Let's set A = ³√(ax² + by² + cz²)
  let A := (a * x^2 + b * y^2 + c * z^2)^((1: ℝ)/3)
  -- We use the same calculation to show that ³√a = A/x, ³√b = A/y, and ³√c = A/z, so we create a general lemma that can be applied in each case
  have h_lemma (a b c x y z: ℝ) (h_apos: a > 0) (h_bpos: b > 0) (h_cpos: c > 0)
    (h_xpos: x > 0) (h_ypos: y > 0) (h_zpos: z > 0)
    (h_ab : a * x^3 = b * y^3) (h_bc : b * y^3 = c * z^3) (h_recip : 1 / x + 1 / y + 1 / z = 1) := by calc
      (a * x^2 + b * y^2 + c * z^2)^((1:ℝ)/3)/x = (a * x^3/x + b * y^3/y + c * z^3/z)^((1:ℝ)/3)/x := by
        rw [pow_succ x 2, pow_succ y 2, pow_succ z 2]
        repeat rw [mul_div_assoc]
        repeat rw [div_self, mul_one]
        all_goals positivity
      _ = (a * x^3 * (1/x + 1/y + 1/z))^((1: ℝ)/3)/x := by
        rw [←h_bc, ←h_ab]
        repeat rw [div_eq_mul_one_div (a * x^3)]
        rw [mul_add, mul_add]
      _ = a^((1: ℝ)/3) := by
        rw [h_recip, mul_one, mul_rpow, ←rpow_natCast, ←rpow_mul]
        field_simp
        all_goals positivity
  -- Given the provided equalities, we obtain A = x³√a
  -- Further, ³√a = A/x
  have hx: A/x = a^((1: ℝ)/3) := by apply h_lemma <;> assumption
  -- Similarly, A = y³√b, so ³√b = A/y
  have hy: A/y = b^((1: ℝ)/3) := by
    rw [show A = (b * y^2 + c * z^2 + a * x^2)^((1: ℝ)/3) from by ring_nf]
    apply h_lemma <;> try assumption
    rwa [add_comm, ←add_assoc]
  -- And ³√c = A/z
  have hz: A/z = c^((1: ℝ)/3) := by
    rw [show A = (c * z^2 + a * x^2 + b * y^2)^((1: ℝ)/3) from by ring_nf]
    apply h_lemma <;> try assumption
    rwa [add_comm, ←add_assoc, add_comm, ←add_assoc]  
  -- And therefore ³√a + ³√b + ³√c = A/x + A/y + A/z = A(1/x + 1/y + 1/z)
  rw [←hx, ←hy, ←hz] 
  rw [show A = A * 1 from Eq.symm $ mul_one A]
  repeat rw [mul_div_assoc]
  rw [←mul_add, ←mul_add, h_recip, mul_one]