import Mathlib

open Real

/-Given positive real numbers $a, b, c$, prove that

$$
\frac{8}{(a+b)^{2}+4 a b c}+\frac{8}{(a+c)^{2}+4 a b c}+\frac{8}{(b+c)^{2}+4 a b c}+a^{2}+b^{2}+c^{2} \geq \frac{8}{a+3}+\frac{8}{b+3}+\frac{8}{c+3}
$$-/
theorem inequalities_605153 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
8 / ((a + b) ^ 2 + 4 * a * b * c) + 8 / ((a + c) ^ 2 + 4 * a * b * c) +
8 / ((b + c) ^ 2 + 4 * a * b * c) + a ^ 2 + b ^ 2 + c ^ 2 ≥
8 / (a + 3) + 8 / (b + 3) + 8 / (c + 3) := by
-- According to the reference answer, we first need to prove the following key lemma
  rw [ge_iff_le]; have lm : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → 8 / (z + 3) ≤
  8 / ((x + y) ^ 2 + 4 * x * y * z) + (x ^ 2 + y ^ 2) / 2 := by
    intro x y z xpos ypos zpos; calc
      _ = 8 / (z + 1 + 2) := by ring_nf
    -- Apply AM-GM inequality to $z+1$ and $2$
      _ ≤ 4 / √ (2 * (z + 1)) := by
        nth_rw 2 [← mul_div_mul_left _ _ (show (2:ℝ)≠0 by simp)]; norm_num
        rw [div_le_div_iff_of_pos_left]; nth_rw 2 [mul_comm]; apply two_mul_le_add_of_sq_eq_mul
        any_goals positivity
        rw [← sqrt_mul, sq_sqrt]; all_goals positivity
      _ = 2 * sqrt (2 / (z + 1)) := by
        nth_rw 2 [← mul_div_mul_left _ _ (show (2:ℝ)≠0 by simp)]; norm_num
        rw [← mul_div_assoc, show √4 = 2 by rw [sqrt_eq_iff_eq_sq]; all_goals linarith]
        congr; norm_num
    -- Apply AM-GM inequality to the two fractions on RHS
      _ ≤ 4 / ((x ^ 2 + y ^ 2) * (z + 1)) + (x ^ 2 + y ^ 2) / 2 := by
        apply two_mul_le_add_of_sq_eq_mul; any_goals positivity
        rw [sq_sqrt]; field_simp; ring; positivity
      _ ≤ _ := by
        simp; rw [← mul_div_mul_left _ _ (show (2:ℝ)≠0 by simp), ← mul_assoc]; norm_num; gcongr
        rw [mul_add, mul_one]; nth_rw 3 [add_comm]; apply add_le_add
        -- Apply AM-GM inequality to $x$ and $y$
        · rw [two_mul, add_sq', mul_assoc]; simp; apply two_mul_le_add_of_sq_eq_mul
          any_goals positivity
          ring
      -- Apply AM-GM inequality to $x$ and $y$
        rw [mul_le_mul_right, show (4:ℝ) = 2*2 by norm_num, mul_assoc, mul_assoc, mul_le_mul_left]
        apply two_mul_le_add_of_sq_eq_mul; any_goals positivity
        ring
-- Apply the key lemma lm to $a$, $b$ and $c$ in three different orders, then the inequality in the main goal will follow from linarith
  have ale := lm a b c ha hb hc; have ble := lm b c a hb hc ha; have cle := lm a c b ha hc hb
  rw [show 4*b*c*a = 4*a*b*c by ring] at ble; rw [show 4*a*c*b = 4*a*b*c by ring] at cle; calc
    _ ≤  8 / ((a + b) ^ 2 + 4 * a * b * c) + (a ^ 2 + b ^ 2) / 2 +
    (8 / ((b + c) ^ 2 + 4 * a * b * c) + (b ^ 2 + c ^ 2) / 2) +
    (8 / ((a + c) ^ 2 + 4 * a * b * c) + (a ^ 2 + c ^ 2) / 2) := by linarith
    _ = _ := by ring