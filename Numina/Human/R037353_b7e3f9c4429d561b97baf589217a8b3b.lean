import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that


$$

\frac{2 a}{a^{2}+b c}+\frac{2 b}{b^{2}+c a}+\frac{2 c}{c^{2}+a b} \leq \frac{a}{b c}+\frac{b}{c a}+\frac{c}{a b} .

$$
 -/
theorem inequalities_236749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a / (a^2 + b * c) + 2 * b / (b^2 + c * a) + 2 * c / (c^2 + a * b) ≤
    a / (b * c) + b / (c * a) + c / (a * b) := by
    -- we first show that 2a/(a^2+bc) ≤ 1/2 * (1/b + 1/c)
    have h0: ∀ a b c:ℝ, 0<a → 0<b → 0<c → 2*a/(a^2+b*c) ≤ 1/2 * (1/b + 1/c) := by
      intro a b c ha hb hc
      field_simp
      apply (mul_le_mul_right (a:=2*b*c*(a^2+b*c)) (by apply mul_pos; nlinarith; nlinarith)).mp
      conv_lhs =>
        calc _
        _ = 2 * a  * (2 * b * c * ((a ^ 2 + b * c)/ (a ^ 2 + b * c))) := by ring_nf
        _ = 2 * a  * 2 * b * c := by rw [div_self (by apply ne_of_gt; nlinarith)]; ring_nf
      conv_rhs =>
        calc _
        _ = (c + b) * ((2 * b * c)/(2 * b * c)  * (a ^ 2 + b * c)) := by ring_nf
        _ = (c + b) * (a ^ 2 + b * c) := by rw [div_self (by apply ne_of_gt; nlinarith)]; ring_nf
      suffices 0 ≤ a ^ 2 * b + a ^ 2 * c + b * c ^ 2 + b ^ 2 * c - a * b * c * 4 by linarith
      conv_rhs =>
        calc _
        _ = b*(a-c)^2+c*(a-b)^2 := by ring_nf;
      apply add_nonneg; nlinarith; nlinarith

    -- now we show 1/b + 1/c ≤ 1/2 * (2a/bc + b/ca + c/ab)
    have h1: ∀ a b c:ℝ, 0<a → 0<b → 0<c → 1/b + 1/c ≤ 1/2 * (2*a/(b*c) + b/(c*a) + c/(a*b)) := by
      intro a b c ha hb hc
      apply (mul_le_mul_right (a:=2*a*b*c) (by apply mul_pos; nlinarith; nlinarith)).mp
      conv_lhs =>
        calc _
        _ = 2 * a * c * (b/ b) + 2 * a * b * (c/ c) := by ring_nf
        _ = 2 * a * (c + b)  := by rw [div_self (by apply ne_of_gt; nlinarith), div_self (by apply ne_of_gt; nlinarith)]; ring_nf
      conv_rhs =>
        calc _
        _ = a * 2 * a * (b * c/ (b * c)) + b * b * (c * a/ (c * a)) + c * c * (a * b/ (a * b)) := by ring_nf
        _ = 2 * a^2 + b^2 + c^2 := by rw [div_self (by apply ne_of_gt; nlinarith), div_self (by apply ne_of_gt; nlinarith), div_self (by apply ne_of_gt; nlinarith)]; ring_nf
      suffices 0 ≤ 2*a^2 + b^2 + c^2 - 2*a*(c+b) by linarith
      conv_rhs =>
        calc _
        _ = (a-b)^2 + (a-c)^2 := by ring_nf;
      nlinarith
    -- now we can combine the lemmas into a result
    calc _
    _ ≤ 1/2 * (1/b + 1/c) + 1/2 * (1/c + 1/a) + 1/2 * (1/a + 1/b) := by linarith [h0 a b c ha hb hc, h0 b c a hb hc ha, h0 c a b hc ha hb]
    _ ≤ 1/2 * (1/2* (2*a/(b*c) + b/(c*a) + c/(a*b))) + 1/2 * (1/2*(2*b/(c*a) + c/(a*b) + a/(b*c))) + 1/2 * (1/2*(2*c/(a*b) + a/(b*c) + b/(c*a))) := by linarith [h1 a b c ha hb hc, h1 b c a hb hc ha, h1 c a b hc ha hb]
    _ =  a / (b * c) + b / (c * a) + c / (a * b) := by ring_nf