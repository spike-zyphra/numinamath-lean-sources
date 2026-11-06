import Mathlib

/- 4.2.23 Given that $a, b, c, d$ are non-negative real numbers, and $ab + bc + cd + da = 1$. Prove:

$$

\frac{a^{3}}{b+c+d}+\frac{b^{3}}{c+d+a}+\frac{c^{3}}{d+a+b}+\frac{d^{3}}{a+b+c} \geqslant \frac{1}{3} .

$$
 -/
theorem inequalities_175857 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a * b + b * c + c * d + d * a = 1) :
    1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) +
    d ^ 3 / (a + b + c) := by
  -- we first need an auxillary am-gm lemma
  have h1: ∀ a b c d:ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a*b+b*c+c*d+d*a=1 → 2/3 * a^2 ≤ a^3/(b+c+d) + a*(b+c+d)/9 := by
    intro a b c d h
    have q:= Real.geom_mean_le_arith_mean2_weighted (w₁:=1/2) (w₂:=1/2) (p₁:=a^3/(b+c+d)) (p₂:=a*(b+c+d)/9) (by norm_num) (by norm_num) (by apply div_nonneg; exact pow_nonneg h.left _; linarith) (by nlinarith) (by norm_num)
    have q':2 * (a ^ 3 / (b + c + d)) ^ ((1:ℝ) / 2) * (a * (b + c + d) / 9) ^ ((1:ℝ) / 2) ≤ (a ^ 3 / (b + c + d)) + (a * (b + c + d) / 9) := by linarith
    convert_to 2 * (a ^ 3 / (b + c + d)) ^ ((1:ℝ) / 2) * (a * (b + c + d) / 9) ^ ((1:ℝ) / 2) ≤ (a ^ 3 / (b + c + d)) + (a * (b + c + d) / 9)
    conv_rhs =>
      calc _
      _ = 2 * (a ^ 3 / (b + c + d) * a * (b + c + d) / 9) ^ ((1:ℝ) / 2) := by rw [mul_assoc, ← Real.mul_rpow (by apply div_nonneg; apply pow_nonneg h.left; linarith) (by nlinarith)]; ring_nf
      _ = 2 * (a ^ 4 * ((b + c + d)/ (b + c + d)) / 9) ^ ((1:ℝ) / 2) := by ring_nf
      _ = 2 * (a ^ 4 / 9) ^ ((1:ℝ) / 2) := by rw [div_self (by (simp; intro h'; apply (add_eq_zero_iff_of_nonneg (by linarith) (by linarith)).mp at h'; obtain ⟨hl, hr⟩ := h'; apply (add_eq_zero_iff_of_nonneg (by linarith) (by linarith)).mp at hl; rw [hr, hl.left, hl.right] at h; simp at h))]; ring_nf
      _ = 2 * ((a ^ 2 / 3)^(2:ℝ)) ^ ((1:ℝ) / 2) := by ring_nf; rw[Real.mul_rpow (x:=a^2) (by nlinarith) (by norm_num)]; norm_num; ring_nf;
      _ = 2 * (a ^ 2 / 3) := by rw [← Real.rpow_mul (by nlinarith)]; ring_nf; norm_num; ring_nf;
      _ = 2/3 * a^2 := by ring_nf
    assumption
  -- let's sum h1 for permuations of a,b,c,d
  have h1a := h1 a b c d ⟨ha, ⟨hb, ⟨hc, ⟨hd, h⟩⟩⟩⟩
  have h1b := h1 b c d a ⟨hb, ⟨hc, ⟨hd, ⟨ha, by linarith⟩⟩⟩⟩
  have h1c := h1 c d a b ⟨hc, ⟨hd, ⟨ha, ⟨hb, by linarith⟩⟩⟩⟩
  have h1d := h1 d a b c ⟨hd, ⟨ha, ⟨hb, ⟨hc, by linarith⟩⟩⟩⟩

  have h1abcd: 2/3 * a^2 + 2/3 * b^2 + 2/3 * c^2 + 2/3 * d^2 ≤ a ^ 3 / (b + c + d) + a * (b + c + d) / 9 +
    b ^ 3 / (c + d + a) + b * (c + d + a) / 9 +
    c ^ 3 / (d + a + b) + c * (d + a + b) / 9 +
    d ^ 3 / (a + b + c) + d * (a + b + c) / 9 := by
    linarith
  -- moving appropriate terms around we can get the right side of the final inequality
  have h2: 2 / 3 * a ^ 2 + 2 / 3 * b ^ 2 + 2 / 3 * c ^ 2 + 2 / 3 * d ^ 2 - a * (b+c+d)/9 - b * (c+d+a)/9 - c * (d+a+b)/9 - d * (a+b+c)/9
  ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by linarith
  -- transitivity
  suffices 1/3 ≤ 2/3 * a^2 + 2/3 * b^2 + 2/3 * c^2 + 2/3 * d^2 - a * (b+c+d)/9 - b * (c+d+a)/9 - c * (d+a+b)/9 - d * (a+b+c)/9 by
    linarith
  -- now we calc bottom up
  calc (1:ℝ)/3
  _ = 5/9 * 1 - 2/9 := by norm_num
  _ = 5/9 * (a*b+b*c+c*d+d*a) - 2/9 := by rw [h]
  _ ≤ 5/9 * (a^2 + b^2 + c^2 + d^2) - 2/9 := by
    simp
    suffices 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - (a * b + b * c + c * d + d * a) by linarith
    conv_rhs =>
      calc _
      _ = ((a-b)^2+(b-c)^2+(c-d)^2+(d-a)^2)/2 := by ring_nf
    nlinarith
  _ ≤ 5/9 * (a^2 + b^2 + c^2 + d^2) - 2/9 + ((a-c)^2+(b-d)^2)/9 := by simp; nlinarith;
  _ = 5/9 * (a^2 + b^2 + c^2 + d^2) - 2/9 + (a^2+c^2-2*a*c+b^2+d^2-2*b*d)/9 := by ring_nf
  _ = 2/3 * (a^2 + b^2 + c^2 + d^2) - 2 * (1+a*c+b*d)/9 := by ring_nf
  _ = 2/3 * (a^2 + b^2 + c^2 + d^2) - 2 * (a*b+b*c+c*d+d*a+a*c+b*d)/9 := by rw [h]
  _ = 2/3 * a^2 + 2/3 * b^2 + 2/3 * c^2 + 2/3 * d^2 - a * (b+c+d)/9 - b * (c+d+a)/9 - c * (d+a+b)/9 - d * (a+b+c)/9 := by ring_nf