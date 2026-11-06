import Mathlib

/- Let $a, b$ be two distinct real numbers and let $c$ be a positive real number such that
$$
a^{4}-2019 a=b^{4}-2019 b=c .
$$
Prove that $-\sqrt{c} < a b < 0$.-/
theorem algebra_605619{a b c: ℝ}(aneb: a ≠ b)
  (cpos: 0 < c)(heq: a^4-2019*a = b^4 - 2019*b ∧ b^4-2019*b = c):
  -√c < a*b ∧ a*b < 0 := by
  -- a^4-2019a = b^4-2019b, so 2019(a-b) = (a-b)(a+b)(a^2+b^2)
  -- cancel a-b, we get (a+b)(a^2+b^2) = 2019
  have h1: (a+b)*(a^2+b^2) = 2019 := by
    have h1: 2019*(a-b) = (a^2+b^2)*(a^2-b^2) := by
      nlinarith [heq.left]
    have h2: (a^2+b^2)*(a^2-b^2) = (a+b)*(a^2+b^2)*(a-b) := by ring
    rw [h2] at h1
    -- a ≠ b, so a-b ≠ 0, and we can cancel it from both sides.
    have h3: a-b ≠ 0 := sub_ne_zero_of_ne aneb
    symm
    have := mul_eq_mul_right_iff.mp h1
    simp [h3] at this; simp [this]
  -- from h1, a+b ≠ 0
  have aneb': a+b ≠ 0 := by
    by_contra!
    simp [this] at h1
  -- then 2c = (a^4-2019a)+(b^4-2019b) = -2ab(a^2+ab+b^2)
  have h2: 2*c = -2*a*b*(a^2+a*b+b^2) := calc
    2*c = a^4 - 2019*a + (b^4-2019*b) := by
      simp [heq, two_mul]
    _ = (a^4+b^4) - 2019*(a+b) := by ring
    _ = (a^4+b^4) - (a+b)^2*(a^2+b^2) := by
      -- by h1, 2019 = (a+b)(a^2+b^2)
      rw [← h1]; ring
    _ = _ := by ring
  -- thus c = -ab(a^2+ab+b^2)
  have h3: c = -(a*b*(a^2+a*b+b^2)) := by linarith [h2]
  -- from h3, we have ab<0
  have h4: a*b < 0 := by
    by_cases h: a*b < 0
    · exact h
    push_neg at h
    -- a^2+ab+b^2 > 0
    have: a^2+a*b+b^2 ≥ 0 := by
      linarith [sq_nonneg a, sq_nonneg b, h]
    -- c > 0, substitute in
    have hh: a*b * (a^2+a*b+b^2) < 0 := by
      rw [h3] at cpos; simp at cpos
      exact cpos
    exact neg_of_mul_neg_left hh this
  -- we show -√c < ab by proving c > (ab)^2
  have h5: -√c < a*b := by
    apply Real.neg_sqrt_lt_of_sq_lt
    -- substitute c=-ab(a^2+ab+b^2) in
    rw [h3]
    apply lt_neg_iff_add_neg.mpr
    have: (a*b)^2+a*b*(a^2+a*b+b^2) = a*b*(a+b)^2 := by ring
    rw [this]
    -- ab (a+b)^2 < 0, because we already prove ab < 0, and a+b ≠ 0
    replace: (a+b)^2 > 0 := pow_two_pos_of_ne_zero aneb'
    nlinarith [h4, this]
  -- done
  exact ⟨h5, h4⟩