import Mathlib

set_option linter.style.longLine true

/- ## Problem 4

Let $k$ be the real cube root of 2.
Find integers A, B, C, a, b, c such that
$\left|\left(A x^{2}+B x+C\right) /\left(a x^{2}+b x+c\right)-k\right|< \left| x- k \right|$
for all non-negative rational $x$.
 -/
theorem algebra_208751 (k : ℝ) (hk : k^3 = 2) :
    ∃ A B C a b c : ℤ, ∀ (x : ℚ), 0 ≤ x →
      |(A * x^2 + B * x + C) / (a * x^2 + b * x + c) - k| < |x - k| := by
    let a : ℤ := 1
    let b : ℤ := 2
    let c : ℤ := 2
    let A := b
    let B := c
    let C := 2 * a
    use A, B, C, a, b, c
    intro x x_nonneg
    field_simp [div_sub', C, a]
    rw [abs_div, div_lt_iff₀ ?pos]
    -- We can factor out the term $(x - k)$
    have key := calc
      (b * x^2 + c * x + 2 * a) - k * (a * x^2 + b * x + c) =
        (b - a * k) * x^2 + (c - b * k) * x + (2 * a - c * k) := by ring
      _ = (x - k) * ((b - a * k) * x + c - a * k^2) := by
        ring_nf
        simp [hk]
        ring_nf
    have pos : 0 < (x : ℝ) ^ 2 + ↑2 * ↑x + ↑2 := by
      simp [(by ring : (x : ℝ) ^ 2 + 2 * ↑x + ↑2 = (x + 1)^2 + 1)]
      nlinarith
    simp [A, B, C, a, b, c] at key ⊢
    rw [mul_comm _ k, key, abs_mul, mul_lt_mul_left ?abs_pos]
    have two_ne_zero : ((2 : ℤ) : ℝ) ≠ 0 := by norm_num
    · have k_lt_two : k < 2 := by nlinarith
      have k_pos : 0 < k := by nlinarith
      calc
      |(2 - k) * ↑x + 2 - k ^ 2| = (2 - k) * ↑x + 2 - k ^ 2 := by
        rw [abs_of_pos ?_]
        simp [sub_eq_add_neg, add_assoc]
        apply lt_add_of_le_of_pos
        · apply mul_nonneg (by linarith) (Rat.cast_nonneg.mpr x_nonneg)
        · nlinarith
      _ < ↑x ^ 2 + 2 * ↑x + 2 := by
        simp [sub_eq_add_neg, add_assoc]
        nth_rewrite 1 [← zero_add ((2 + -k) *x)]
        simp only [add_assoc]
        apply add_lt_add_of_le_of_lt (sq_nonneg _)
        apply add_lt_add_of_le_of_lt
        apply mul_le_mul (by linarith) (le_refl _) (Rat.cast_nonneg.mpr x_nonneg) (by norm_num)
        apply sub_lt_self
        nlinarith
      _ = |↑x ^ 2 + 2 * ↑x + 2| := by
        rw [abs_of_pos pos]
    -- We show that $|x - k| > 0$ by showing $x \ne k$ since $k $ is irrational
    · have irrational_k : Irrational k := by
        apply @irrational_nrt_of_n_not_dvd_multiplicity k 3 2 (by norm_num) 2 _ (by simp [hk])
        simp [multiplicity_self]
      rw [abs_pos, sub_ne_zero]
      symm
      exact irrational_k.ne_rat x
    · have pos : 0 < (x : ℝ) ^ 2 + ↑2 * ↑x + ↑2 := by
        have helper : (x + 1)^2 + 1 = (x : ℝ) ^ 2 + 2 * ↑x + ↑2 := by ring
        simp [← helper]
        nlinarith
      rw [abs_of_pos]
      · exact pos
      · exact pos
