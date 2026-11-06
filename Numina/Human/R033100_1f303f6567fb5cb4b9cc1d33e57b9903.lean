import Mathlib

/- Solve
\[\frac{|x^2 - 81|}{x^2 - 36x} < 0.\]-/
theorem algebra_21485 (x : ℝ) (_ : x^2 - 36*x ≠ 0) :
    |x^2 - 81| / (x^2 - 36 * x) < 0 ↔ (0 < x ∧ x < 9) ∨ (9 < x ∧ x < 36) := by
  -- Note that $|x^2 - 81| \ge 0$ for all $x,$ with $|x^2 - 81| = 0$ only for $x = \pm 9.$
  have ne_zero_of_ne_nine_and_ne_neg_nine {x : ℝ} (hx1 : x ≠ 9) (hx2 : x ≠ -9) : |x ^ 2 - 81| ≠ 0 := by
    intro h
    simp at h
    have : (x - 9) * (x + 9) = 0 := by linear_combination h
    simp at this
    contrapose! this
    constructor
    . contrapose! hx1
      linear_combination hx1
    contrapose! hx2
    linear_combination hx2
  constructor
  swap
  -- Verify that (0 < x ∧ x < 9) ∨ (9 < x ∧ x < 36) satify |x^2 - 81| / (x^2 - 36 * x) < 0.
  . rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
    . have : 0 < |x ^ 2 - 81| := by
        rw [lt_iff_le_and_ne]
        constructor
        . positivity
        symm
        apply ne_zero_of_ne_nine_and_ne_neg_nine
        all_goals linarith
      have : x^2 - 36 * x < 0 := by nlinarith
      apply div_neg_of_pos_of_neg
      all_goals assumption
    have : 0 < |x ^ 2 - 81| := by
      rw [lt_iff_le_and_ne]
      constructor
      . positivity
      symm
      apply ne_zero_of_ne_nine_and_ne_neg_nine
      all_goals linarith
    have : x^2 - 36 * x < 0 := by nlinarith
    apply div_neg_of_pos_of_neg
    all_goals assumption
  intro h
  have : 0 < |x ^ 2 - 81| := by
    rw [lt_iff_le_and_ne]
    constructor
    . positivity
    symm
    intro habs
    rw [habs] at h
    norm_num at h
  -- The denominator factors as $x(x - 36).$  This is negative only for $0 < x < 36.$
  have : x ^ 2 - 36 * x < 0 := by
    contrapose! h
    positivity
  have : (x - 36) * x < 0 := by
    convert this using 1
    ring
  have : 0 < x ∧ x < 36 := by constructor <;> nlinarith
  -- Thus, the solution is
  -- \[x \in \boxed{(0,9) \cup (9,36)}.\]-/
  rcases le_or_lt x 9 with hx9 | hx9
  . left
    constructor
    . exact this.1
    rw [lt_iff_le_and_ne]
    constructor
    . exact hx9
    intro hx9
    norm_num [hx9] at h
  right
  exact ⟨hx9, this.2⟩
