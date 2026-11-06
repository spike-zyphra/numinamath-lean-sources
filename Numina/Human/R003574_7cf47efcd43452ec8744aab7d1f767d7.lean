import Mathlib

/- 9.232 Let $x_{1}>0$ be a root of the equation $a x^{2}+b x+c=0$.

Prove: there exists a root $x_{2}$ of the equation $c x^{2}+b x+a=0$ such that $x_{1}+x_{2} \geq 2$. -/
theorem algebra_197372 {a b c x1: ℝ} (ha : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (x1pos : x1 > 0) (hroots : a * x1 ^ 2 + b * x1 + c = 0) :
    ∃ x2, c * x2 ^ 2 + b * x2 + a = 0 ∧ x1 + x2 ≥ 2 := by 
  --use 1 / x1 as a candidate
  use (1 / x1)
  field_simp
  ring_nf
  constructor
  --we have that since x1 is a root then by factoring x1 out, 1 / x1 is a root of cx^2+bx+a.
  · have : x1 * (a * x1 ^ 2 + b * x1 + c) = 0 := by 
      rw[hroots]
      simp
    ring_nf at this
    linarith
  --by amgm inequality we have 1 = √x1*1/x1 ≤ 1/2 (x1 + 1 / x1), yielding the claim.
  · have amgm : x1 ^ (1/(2 : ℝ)) * (1 / x1) ^ (1/(2 : ℝ)) ≤ (1/(2 : ℝ)) * x1 + (1/(2 : ℝ)) * (1 / x1) := by 
      exact Real.geom_mean_le_arith_mean2_weighted (by linarith) (by linarith) (by linarith) (by ring_nf; exact le_of_lt (inv_pos_of_pos x1pos)) (by linarith)
    have : (x1 * (1 / x1)) ^ (1 / 2) ≤ 1 / 2 * (x1 + 1 / x1) := by 
      ring_nf at amgm ⊢
      rw[← Real.mul_rpow (by linarith) (by ring_nf; exact le_of_lt (inv_pos_of_pos x1pos)), mul_comm, (by field_simp : x1⁻¹ * x1 = 1)] at amgm
      norm_num at amgm
      linarith
    rw[← mul_div_assoc, mul_one, div_self (by linarith)] at this
    field_simp at this ⊢
    rw[← sq] at this
    have h : 2 * 1 ≤ 2 * ((x1^2 + 1) / (2 * x1)) := mul_le_mul_of_nonneg_left this (by norm_num)
    rw[mul_one] at h
    rw[(by ring_nf : 2 * ((x1 ^ 2 + 1) / (2 * x1)) = ((x1 ^ 2 + 1) / x1))] at h
    exact h