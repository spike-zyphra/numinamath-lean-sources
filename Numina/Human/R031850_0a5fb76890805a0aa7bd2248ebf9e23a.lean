import Mathlib

open Real Set
open scoped BigOperators

/- Find the range of the function \[f(x) = \frac{x}{x^2-x+1},\]where $x$ can be any real number. (Give your answer in interval notation.) -/
theorem algebra_16170 (f : ℝ → ℝ) (hf : f = λ x => x / (x ^ 2 - x + 1)) :
  range f = {y | -1/3 ≤ y ∧ y ≤ 1} := by
  rw [range]
  ext h
  constructor
  . -- proof of forward
    -- Let $y$ be a number in the range of $f.$ This means that there is a real number $x$ such that \[y = \frac{x}{x^2-x+1}.\]
    intro hx; simp;
    rw [hf] at hx; simp at hx
    if heq0 : h = 0 then
      rw [heq0]
      constructor <;> linarith
    else
    rcases hx with ⟨y, hy⟩
    symm at hy
    -- Multiplying both sides by $x^2-x+1$ and rearranging, we get the equation \[yx^2-(y+1)x+y=0.\]
    rw [eq_div_iff_mul_eq] at hy
    apply_fun (. - y) at hy; simp at hy
    symm at hy
    replace hy := calc
      0 = h * (y ^ 2 - y + 1) - y := hy
      _ = h * y * y + (-h - 1) * y + h := by ring_nf
    symm at hy
    -- this equation has a real solution for $x$ if and only if the discriminant of this quadratic is nonnegative. Therefore, the range of $f$ consists exactly of the values of $y$ which satisfy \[(y+1)^2 - 4y^2 \ge 0,\]or \[0 \ge 3y^2 - 2y - 1.\]
    rw [mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at hy
    rw [discrim] at hy
    rw [show (-h - 1) ^ 2 - 4 * h * h = -(3 * h + 1) * (h - 1) by ring_nf] at hy
    replace hy := calc
      -(3 * h + 1) * (h - 1) = (2 * h * y + (-h - 1)) ^ 2 := hy
      _ ≥ 0 := by
        rw [ge_iff_le]
        apply sq_nonneg
    rw [ge_iff_le] at hy
    -- This quadratic factors as \[0 \ge (3y+1)(y-1),\]which means that the solutions to the inequality are given by $-\tfrac13 \le y \le 1.$ Therefore, the range of $g$ is the closed interval $\boxed{[-\tfrac13, 1]}.$
    if h_minus_one_lt_0 : (h - 1) < 0 then
      apply nonpos_of_mul_nonneg_left at hy
      replace hy := hy h_minus_one_lt_0
      have h_ge_frac_1_3 : -1 / 3 ≤ h := by linarith
      have h_le_1 : h ≤ 1 := by linarith
      exact ⟨h_ge_frac_1_3, h_le_1⟩
    else
      replace h_ge_1 : 1 ≤ h := by linarith
      if h_eq_1 : h = 1 then
        rw [h_eq_1]
        constructor <;> linarith
      else
        have h_ge_1_clone := h_ge_1
        rw [le_iff_eq_or_lt] at h_ge_1
        rcases h_ge_1 with heq1_2 | hlt1
        symm at heq1_2; contradiction
        replace hlt1 : 0 < h - 1 := by linarith
        rw [mul_nonneg_iff_left_nonneg_of_pos] at hy
        constructor <;> linarith
        linarith
    simp
    exact heq0
    -- Since $x^2-x+1 = (x-\tfrac12)^2 + \tfrac34 > 0$ for all $x,$ our steps are reversible
    rw [show y ^ 2 - y + 1  = 1 * y * y + (-1 * y) + 1 by ring_nf, mul_assoc]
    apply quadratic_ne_zero_of_discrim_ne_sq
    rw [discrim]
    ring_nf
    intro s
    have snonneg := sq_nonneg s
    linarith
  . -- proof of backward
    intro hx; simp at hx
    rw [hf]; simp
    if heq0 : h = 0 then
      exists 0
      rw [heq0]
      simp
    else
      -- y is get from real solution for quadratic equation
      let y := (h * h⁻¹ * (1 / 2) + √(1 + (h * 2 - h ^ 2 * 3)) * h⁻¹ * (1 / 2) + h⁻¹ * (1 / 2) : ℝ)
      exists y
      rw [div_eq_iff_mul_eq]
      apply eq_of_sub_eq_zero
      rw [show h * (y ^ 2 - y + 1) - y = h * y * y + (-h - 1) * y + h by ring_nf]
      rw [mul_assoc, quadratic_eq_zero_iff]
      -- discrim is $√((h+1)^2 - 4*h^2)$
      case h.s =>
        exact (√((h+1)^2 - 4*h^2))
      ring_nf; repeat simp
      exact heq0
      rw [discrim]; ring_nf
      -- factor as $-(3 * h + 1) * (h - 1)$
      rw [show 1 + (h * 2 - h ^ 2 * 3) = -(3 * h + 1) * (h - 1) by ring_nf]
      rw [sq_sqrt]
      have h_minus_1_le_0 : h - 1 ≤ 0 := by linarith
      have neg_triple_h_plus_one_le_0 : -(3 * h + 1) ≤ 0 := by linarith
      apply mul_nonneg_of_nonpos_of_nonpos
      repeat linarith
      -- $y^2 - y + 1$ is always ≠ 0
      have hy : y ^ 2 - y + 1 = 1 * y * y + (-1) * y + 1 := by ring_nf
      rw [hy, mul_assoc]
      apply quadratic_ne_zero_of_discrim_ne_sq
      rw [discrim]; ring_nf
      intro s
      have s_pow_2_ge_0 := sq_nonneg s
      linarith
