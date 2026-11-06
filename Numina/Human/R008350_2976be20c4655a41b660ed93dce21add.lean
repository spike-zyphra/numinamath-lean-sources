import Mathlib

open Real

/-Let $x, y$ and $z$ be positive real numbers such that $\sqrt{x}+\sqrt{y}+\sqrt{z}=1$. Prove that

$$
\frac{x^{2}+y z}{\sqrt{2 x^{2}(y+z)}}+\frac{y^{2}+z x}{\sqrt{2 y^{2}(z+x)}}+\frac{z^{2}+x y}{\sqrt{2 z^{2}(x+y)}} \geq 1
$$-/
theorem inequalities_605165 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(h : √x + √y + √z = 1) : 1 ≤ (x ^ 2 + y * z) / √(2 * x ^ 2 * (y + z)) +
(y ^ 2 + z * x) / √(2 * y ^ 2 * (z + x)) + (z ^ 2 + x * y) / √(2 * z ^ 2 * (x + y)) := by
-- Assume w. l. o. g. that $x≥y≥z$
  wlog zlex : z ≤ x
  · specialize this z y x hz hy hx (by rw [← h]; ring) (by linarith); calc
      _ ≤ _ := this
      _ = _ := by ring_nf
  wlog zley : z ≤ y
  · specialize this x z y hx hz hy (by rw [← h]; ring) (by linarith) (by linarith); calc
      _ ≤ _ := this
      _ = _ := by ring_nf
  wlog ylex : y ≤ x
  · specialize this y x z hy hx hz (by rw [← h]; ring) (by linarith) (by linarith) (by linarith)
    calc _ ≤ _ := this
      _ = _ := by ring_nf
-- According to the reference answer, we need the following auxillary inequality
  have aux : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → ((a - b) * (a - c)) / √(2 * a ^ 2 * (b + c))
  + (√b + √c) / 2 ≤ (a ^ 2 + b * c) / √(2 * a ^ 2 * (b + c)) := by
  -- Rearrange terms on RHS and simplify
    intro a b c apos bpos cpos; rw [← le_sub_iff_add_le', div_sub_div_same]
    rw [show (a^2+b*c-(a-b)*(a-c)) = a*(b+c) by ring]; nth_rw 3 [mul_comm]
    rw [mul_assoc, sqrt_mul, sqrt_sq, mul_div_mul_left, div_le_div_iff₀]
  -- Take square on both sides and simplify
    rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by norm_num), mul_pow, sq_sqrt]
    rw [← mul_assoc]; nth_rw 3 [mul_comm]; rw [mul_pow]; nth_rw 3 [pow_two]
    rw [← mul_assoc, mul_le_mul_right]; nth_rw 2 [mul_comm, pow_two]
    rw [← mul_assoc, mul_le_mul_right, add_sq, sq_sqrt, sq_sqrt, ← sub_nonneg]
  -- Rewrite RHS to a square
    ring_nf; calc _ ≤ (√b - √c) ^ 2 := by positivity
      _ = _ := by rw [sub_sq, sq_sqrt, sq_sqrt]; ring; all_goals positivity
    all_goals positivity
-- Apply the lemma to $x$, $y$ and $z$ in different orders
  have xyz := aux x y z hx hy hz; have yzx := aux y z x hy hz hx; have zxy := aux z x y hz hx hy
-- Add the three inequalities and rewrite the goal by transitivity
  apply le_trans _ (add_le_add (add_le_add xyz yzx) zxy); rw [← add_assoc, add_add_add_comm]
  nth_rw 2 [add_comm]; rw [← add_assoc]; nth_rw 3 [add_comm]; rw [add_assoc]
-- Rearrange terms and use the assumption h to simplify, then use various linear arithmetics to finish the goal
  rw [div_add_div_same, div_add_div_same, add_assoc, add_assoc, add_comm]
  apply le_add_of_le_of_nonneg; rw [← add_assoc, add_comm]
  apply le_add_of_le_of_nonneg; rw [← h]; ring_nf; rfl
  · rw [← neg_le_iff_add_nonneg', neg_div', neg_mul_eq_mul_neg, neg_sub]
    rw [show (z-x)*(z-y) = (x-z)*(y-z) by ring]; calc
      _ ≤ (x - y) * (y - z) / √(2 * z ^ 2 * (x + y)) := by
        rw [mul_comm]; apply div_le_div_of_nonneg_left
        apply mul_nonneg; any_goals linarith
        positivity; suffices : z ^ 2 * (x + y) ≤ y ^ 2 * (z + x)
        · rw [mul_assoc, mul_assoc]; gcongr
        rw [mul_add, mul_add, add_comm]; apply add_le_add
        · rw [mul_comm, pow_two, ← mul_assoc, pow_two]; gcongr
        gcongr
      _ ≤ _ := by gcongr; linarith
  apply div_nonneg; apply mul_nonneg; any_goals linarith
  positivity