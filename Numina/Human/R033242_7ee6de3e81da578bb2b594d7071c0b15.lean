import Mathlib

/- 31. (8) The numbers $a, b$, and $c$ lie in the interval $[2,4]$. Prove the inequality:


$$

\frac{2}{a+b^{2}+c^{3}}+\frac{2}{b+c^{2}+a^{3}}+\frac{2}{c+a^{2}+b^{3}} \leqslant \frac{3}{a+b+c} .

$$
 -/
theorem inequalities_117037
    (a b c : ℝ)
    (ha : a ∈ Set.Icc 2 4)
    (hb : b ∈ Set.Icc 2 4)
    (hc : c ∈ Set.Icc 2 4) :
    2 / (a + b ^ 2 + c ^ 3) + 2 / (b + c ^ 2 + a ^ 3) +
    2 / (c + a ^ 2 + b ^ 3) ≤
    3 / (a + b + c)
  := by

    -- move 3 / (a + b + c) to left side
    rw [←tsub_nonpos]

    -- subtract 1 / (a + b + c) from each term
    convert_to (2 / (a + b ^ 2 + c ^ 3) - 1 / (a + b + c)) + (2 / (b + c ^ 2 + a ^ 3) - 1 / (a + b + c)) + (2 / (c + a ^ 2 + b ^ 3) - 1 / (a + b + c)) ≤ 0
    · ring

    -- each term is the same up to permutation of variables
    convert_to (2 / (a + b ^ 2 + c ^ 3) - 1 / (a + b + c)) + (2 / (b + c ^ 2 + a ^ 3) - 1 / (b + c + a)) + (2 / (c + a ^ 2 + b ^ 3) - 1 / (c + a + b)) ≤ 0
    · ring

    -- each term is nonpositive
    have nonpositive : ∀ {a b c : ℝ}, a ∈ Set.Icc 2 4 → b ∈ Set.Icc 2 4 → c ∈ Set.Icc 2 4 → (2 / (a + b ^ 2 + c ^ 3) - 1 / (a + b + c)) ≤ 0 := by
      intro a b c ha hb hc
      -- a b c are positive
      have : 0 < a := by linarith only [Set.mem_Icc.mp ha]
      have : 0 < b := by linarith only [Set.mem_Icc.mp hb]
      have : 0 < c := by linarith only [Set.mem_Icc.mp hc]
      -- rewrite to single fraction
      have pos_pows : (a + b ^ 2 + c ^ 3) ≠ 0 := by positivity
      have pos_sum : (a + b + c) ≠ 0 := by positivity
      rw [div_sub_div _ _ pos_pows pos_sum]
      -- we have a / b ≤ 0 if a ≤ 0 ∧ 0 < b
      have div_le_zero : ∀ {x y : ℝ}, x ≤ 0 → 0 < y → x / y ≤ 0 := by
        intro x y hx hy
        rw [←mul_le_mul_left hy, mul_zero, mul_div_cancel₀ x (ne_of_lt hy).symm]
        exact hx

      -- apply to our case
      apply div_le_zero
      -- numerator is nonpositive
      · convert_to a + b * (2 - b) + c * (2 - c ^ 2) ≤ 0
        · ring
        -- we bound each term
        have bound_a : a ≤ 4 := (Set.mem_Icc.mp ha).2
        have bound_b : b * (2 - b) ≤ 0 := by
          nlinarith only [Set.mem_Icc.mp hb]
        have bound_c : c * (2 - c ^ 2) ≤ -4 := by
          nlinarith only [Set.mem_Icc.mp hc]
        -- so we have our bound on sum of terms
        linarith only [bound_a, bound_b, bound_c]
      -- denominator is positive
      · positivity

    -- so their sum is nonpositive
    linarith only [nonpositive ha hb hc, nonpositive hb hc ha, nonpositive hc ha hb]