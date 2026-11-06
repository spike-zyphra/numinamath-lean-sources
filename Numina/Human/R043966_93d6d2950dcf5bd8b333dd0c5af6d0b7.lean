import Mathlib

open Real

/-Soient a, b, $c>0$. Montrer que

$$
\sqrt{\frac{a}{b+c}}+\sqrt{\frac{b}{c+a}}+\sqrt{\frac{c}{a+b}}>2 .
$$-/
theorem inequalities_607625 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
sqrt (a / (b + c)) + sqrt (b / (c + a)) + sqrt (c / (a + b)) > 2 := by
-- Rewrite the strict inequality to two goals
  rw [gt_iff_lt, lt_iff_le_and_ne]
-- According to the reference answer, we prove the following auxillary inequality
  have auxle : ∀ x y z, 0 < x → 0 < y → 0 < z → (2 * x) / (x + y + z) ≤ √ (x / (y + z)) := by
    intro x y z xpos ypos zpos; rw [sqrt_div]
    nth_rw 2 [← mul_div_mul_left _ _ (show 2*√x≠0 by positivity)]
    rw [mul_assoc, mul_self_sqrt, div_le_div_iff_of_pos_left, mul_assoc, add_assoc]
    apply two_mul_le_add_of_sq_eq_mul; any_goals positivity
    rw [mul_pow, sq_sqrt, sq_sqrt]; all_goals positivity
-- Find the condition when equality holds
  have auxeq : ∀ x y z, 0 < x → 0 < y → 0 < z → ((2 * x) / (x + y + z) = √ (x / (y + z)) ↔
  x = y + z) := by
    intro x y z xpos ypos zpos; rw [sqrt_div]; nth_rw 2 [← mul_div_mul_left _ _ (show 2*√x≠0 by positivity)]
    rw [mul_assoc, mul_self_sqrt, div_eq_div_iff, mul_left_cancel_iff_of_pos, add_assoc]
    nth_rw 2 [← sq_sqrt (show 0≤x by positivity)]; nth_rw 2 [← sq_sqrt (show 0≤y+z by positivity)]
    rw [← sub_eq_zero, show 2*√x*√(y+z)-(√x^2+√(y+z)^2) = -(√x-√(y+z))^2 by ring]; simp
    rw [sub_eq_zero, ← pow_left_inj₀ _ _ (show 2≠0 by simp), sq_sqrt, sq_sqrt]; all_goals positivity
-- Apply auxle to $a$, $b$ and $c$ in different orders
  have auxa := auxle a b c ha hb hc; have auxb := auxle b c a hb hc ha; have auxc := auxle c a b hc ha hb
  have sum2 : 2 * a / (a + b + c) + 2 * b / (b + c + a) + 2 * c / (c + a + b) = 2 := by ring_nf; field_simp; ring
-- The unstrict inequality follows from linarith. To prove the strict inequality, we assume the contrary that the two sides are equal
  constructor; linarith; intro h; replace auxa : 2 * a / (a + b + c) = √(a / (b + c)) := by linarith
-- Apply auxeq to find the conditions when equality holds, then use linarith to find a contradiction
  let ha' := auxa; rw [auxeq a b c ha hb hc] at ha'
  replace auxb : 2 * b / (b + c + a) = √(b / (c + a)) := by linarith
  let hb' := auxb; rw [auxeq b c a hb hc ha] at hb'
  replace auxc : 2 * c / (c + a + b) = √(c / (a + b)) := by linarith
  let hc' := auxc; rw [auxeq c a b hc ha hb] at hc'; linarith