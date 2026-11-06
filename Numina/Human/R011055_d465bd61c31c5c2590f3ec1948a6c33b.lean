import Mathlib

/- 3. The product of positive numbers $a, b, c$ and $d$ is 1. Prove the inequality


$$

\frac{a^{4}+b^{4}}{a^{2}+b^{2}}+\frac{b^{4}+c^{4}}{b^{2}+c^{2}}+\frac{c^{4}+d^{4}}{c^{2}+d^{2}}+\frac{d^{4}+a^{4}}{d^{2}+a^{2}} \geqslant 4

$$
 -/
theorem inequalities_220668 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    4 ≤ (a^4 + b^4) / (a^2 + b^2) + (b^4 + c^4) / (b^2 + c^2) +
        (c^4 + d^4) / (c^2 + d^2) + (d^4 + a^4) / (d^2 + a^2) := by
  -- we first show that 2*(a^4 + b^4) ≥ (a^2 + b^2)^2
  have h1: ∀a b:ℝ, (a^2+b^2)^2 ≤ 2*(a^4 + b^4) := by
    intros a b
    nlinarith [sq_nonneg (b^2-a^2)]
  -- then we can apply this to each of the four terms
  calc (a ^ 4 + b ^ 4) / (a ^ 2 + b ^ 2) + (b ^ 4 + c ^ 4) / (b ^ 2 + c ^ 2) + (c ^ 4 + d ^ 4) / (c ^ 2 + d ^ 2) + (d ^ 4 + a ^ 4) / (d ^ 2 + a ^ 2)
  _ ≥ (1/2 * (a^2+b^2)^2) / (a ^ 2 + b ^ 2) + (1/2 * (b^2+c^2)^2) / (b ^ 2 + c ^ 2) + (1/2 * (c^2+d^2)^2) / (c ^ 2 + d ^ 2) + (1/2 * (d^2+a^2)^2) / (d ^ 2 + a ^ 2) := by
    gcongr
    linarith [h1 a b]
    linarith [h1 b c]
    linarith [h1 c d]
    linarith [h1 d a]
  -- then simplify
  _ = 1/2 * (a^2+b^2) * ((a^2+b^2)/(a^2+b^2)) + 1/2 * (b^2+c^2) * ((b^2+c^2)/(b^2+c^2)) + 1/2 * (c^2+d^2) * ((c^2+d^2)/(c^2+d^2)) + 1/2 * (d^2+a^2) * ((d^2+a^2)/(d^2+a^2)) := by ring_nf
  _ = 1/2 * (a^2+b^2) + 1/2 * (b^2+c^2) + 1/2 * (c^2+d^2) + 1/2 * (d^2+a^2) := by repeat rw [div_self (by apply ne_of_gt; nlinarith), mul_one]
  _ = (a^2+b^2)+(c^2+d^2) := by ring_nf
  _ ≥ 2*a*b+2*c*d := by gcongr; nlinarith [sq_nonneg (b-a)]; nlinarith [sq_nonneg (d-c)]
  -- and finish with AM-GM
  _ ≥ 4*√(a*b*c*d) := by
    have q:= Real.geom_mean_le_arith_mean2_weighted (w₁:=1/2) (w₂:=1/2) (p₁:=2*a*b) (p₂:=2*c*d) (by norm_num) (by norm_num) (by nlinarith) (by nlinarith) (by norm_num)
    simp
    apply (mul_le_mul_right (a:=2) (by norm_num)).mpr at q
    rw [← Real.mul_rpow (by nlinarith) (by nlinarith), show 2 * a * b * (2 * c * d) = 2^(2:ℝ) * (a*b*c*d) by ring_nf, Real.mul_rpow (by norm_num) (by nlinarith), ← Real.rpow_mul (by norm_num), mul_div, mul_one, div_self (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow] at q
    ring_nf at q ⊢
    assumption
  _ = 4 := by rw [h]; norm_num;