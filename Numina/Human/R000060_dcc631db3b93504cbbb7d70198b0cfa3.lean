import Mathlib

set_option maxHeartbeats 0

open Real Finset

/- x^2√(yz) ≤ (4x^3+y^3+z^3)/6 -/
lemma aux_4198 {x : ℕ → ℝ} (hx : ∀ i, 0 < x i) :
    x 0 ^ 2 * (x 1 * x 2) ^ (2⁻¹ : ℝ) ≤ 6⁻¹ * (4 * x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3) := by
  -- setting up data for AM-GM inequality
  let y : ℕ → ℝ := fun i => match i with
    | 0 | 1 | 2 | 3 => x 0 ^ 3
    | 4 => x 1 ^ 3
    | 5 => x 2 ^ 3
    | _ => 0
  have hy i (hi : i ≤ 5 := by norm_num) : 0 ≤ y i := by
    interval_cases i <;> simp [y] <;> apply le_of_lt <;> exact pow_pos (hx _) _
  have hy' i (hi : i ≤ 6 := by norm_num) : 0 ≤ ∏ x ∈ range i, y x := by
    apply prod_nonneg
    intro x hx
    simp at hx
    refine hy x ?_
    linarith
  let w : ℕ → ℝ := fun _ => 1 / 6
  have hw : (∑ i ∈ range 6, w i) = 1 := by rw [sum_const]; simp
  -- by weighted AM-GM inequality we have
  -- $\sqrt[6]{x^12y^3z^3}$ ≤ (4x^3+y^3+z^3)/6$
  have H : (∏ i ∈ range 6, y i ^ w i) ^ (∑ i ∈ range 6, w i)⁻¹ ≤
      (∑ i ∈ range 6, w i * y i) / ∑ i ∈ range 6, w i := by
    apply geom_mean_le_arith_mean
    . intro i hi
      simp at hi
      interval_cases i <;> simp [w]
    . apply sum_pos
      intro i hi
      simp at hi
      interval_cases i <;> simp [w]
      exact nonempty_range_succ
    intro i hi
    simp at hi
    interval_cases i <;> simp [y] <;> apply le_of_lt <;> apply pow_pos
    any_goals exact hx 0
    exact hx 1
    exact hx 2
  -- rewrite $\sqrt[6]{x^12y^3z^3}$ ≤ (4x^3+y^3+z^3)/6$ to
  -- $x^2\sqrt{yz} ≤ (4x^3+y^3+z^3)/6 $
  rw [hw, show 1⁻¹ = (1 : ℝ) from inv_one, rpow_one, div_one] at H
  simp [prod_range_succ, w] at H
  conv at H =>
    rw [← mul_rpow (hy 0) (hy 1)]
    rw [← mul_rpow (by have := hy' 2; simpa [prod_range_succ]) (hy 2)]
    rw [← mul_rpow (by have := hy' 3; simpa [prod_range_succ]) (hy 3)]
    rw [← mul_rpow (by have := hy' 4; simpa [prod_range_succ]) (hy 4)]
    rw [← mul_rpow (by have := hy' 5; simpa [prod_range_succ]) (hy 5)]
    lhs
    simp [y]
    lhs
    repeat rw [← mul_pow]
  have : 0 ≤ x 0 * x 0 * x 0 * x 0 * x 1 * x 2 := by
    repeat apply mul_nonneg; swap; apply le_of_lt; apply hx
    apply le_of_lt; apply hx
  rw [← rpow_natCast, ← rpow_mul this] at H
  rw [← pow_two, ← pow_succ, ← pow_succ, show 2+1+1=4 by ring, mul_assoc] at H
  rw [mul_rpow (show 0 ≤ x 0 ^ 4 by apply le_of_lt; apply pow_pos; apply hx)
    (show 0 ≤ x 1 * x 2 by apply le_of_lt; apply mul_pos <;> apply hx)] at H
  rw [← rpow_natCast, ← rpow_mul (show 0 ≤ x 0 from le_of_lt <| hx _)] at H
  have : (3 : ℝ) * 6⁻¹ = 2⁻¹ := by
    field_simp; norm_num
  norm_cast at H
  rw [show (3 : ℝ) * 6⁻¹ = 2⁻¹ by norm_num] at H
  rw [show (4 : ℝ) * 2⁻¹ = 2 by field_simp; norm_num] at H
  simp [sum_range_succ, ← mul_add, y] at H
  rw [← one_mul (x 0 ^ 3), ← add_mul, ← add_mul, ← add_mul] at H
  rw [show 1+1+1+1=(4:ℝ) by norm_num] at H
  exact H

/- Show that for all \( x, y, z > 0 \):
$$
\sum_{cyc} x^{3} \geq \sum_{cyc} x^{2} \sqrt{yz}
$$-/
theorem inequalities_4198 {x : ℕ → ℝ} (hxpos : ∀ i, 0 < x i) :
    ∑ i ∈ range 3, x i ^ 2 * (x ((i + 1) % 3) * x ((i + 2) % 3))^(2⁻¹:ℝ) ≤ ∑ i ∈ range 3, x i ^ 3 := by
  -- use lemma, we have x^2√(yz) ≤ (4x^3+y^3+z^3)/6
  have hx := aux_4198 hxpos
  let y : ℕ → ℝ := fun n => match n with
    | 0 => x 1 | 1 => x 2 | 2 => x 0 | _ => 1
  have hypos : ∀ i, 0 < y i := by
    intro i
    simp [y]
    split <;> first | try apply hxpos
    norm_num
  -- use lemma, we have y^2√(zx) ≤ (4y^3+z^3+x^3)/6
  have hy := aux_4198 hypos
  simp [y] at hy
  let z : ℕ → ℝ := fun n => match n with
    | 0 => x 2 | 1 => x 0 | 2 => x 1 | _ => 1
  have hzpos : ∀ i, 0 < z i := by
    intro i
    simp [z]
    split <;> first | try apply hxpos
    norm_num
  -- use lemma, we have z^2√(xy) ≤ (4z^3+x^3+y^3)/6
  have hz := aux_4198 hzpos
  simp [z] at hz
  simp [sum_range_succ]
  -- combining hx, hy and hz, we can draw a conclusion
  have hxyz := add_le_add (add_le_add hx hy) hz
  apply le_of_le_of_eq hxyz
  ring
