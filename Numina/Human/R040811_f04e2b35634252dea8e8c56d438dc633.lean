import Mathlib

/- Solve \[\frac{2x+4}{x^2+4x-5}=\frac{2-x}{x-1}\]for $x$. -/
theorem algebra_14102 (x : ℝ) (hx : x ≠ 1) :
    (2 * x + 4) / (x ^ 2 + 4 * x - 5) = (2 - x) / (x - 1) ↔ x = -6 := by
  -- notice that we can do factorization to denominator.
  -- x^2+4x-5=(x-1)(x+5). besides, x≠1, so x-1≠0 and we can cancel it on both sides, to get (2x+4)/(x+5)=(2-x)
  have h1: (2*x+4)/(x^2+4*x-5) = (2-x)/(x-1) ↔
    (2*x+4)/(x+5) = 2-x := by
    have ht1: x^2+4*x-5 = (x-1)*(x+5) := by ring
    have ht2: x-1 ≠ 0 := by
      by_contra! hc
      have nhx: x = 1 := by
        rw [← add_zero 1, ← hc]; ring
      rw [nhx] at hx; simp at hx
    have ht3: (2*x+4)/((x-1)*(x+5)) = ((2*x+4)/(x+5)) / (x-1) := by
      field_simp [ht2]; ring
    rw [ht1, ht3]
    constructor <;> intro h
    · have: (2*x+4)/(x+5) = (2*x+4)/(x+5) / (x-1) * (x-1) := by
        symm; exact div_mul_cancel₀ ((2 * x + 4) / (x + 5)) ht2
      rw [this, h]
      exact div_mul_cancel₀ (2 - x) ht2
    · rw [h]
  -- (2x+4)/(x+5) = 2-x, multiply x+5 to both sides, we get 2x+4 = (x+5)(2-x) = -x^2-3x+10
  have h2: x+5 ≠ 0 → ((2*x+4)/(x+5) = 2-x ↔ 2*x+4 = -x^2-3*x+10) := by
    intro xne
    have: (2*x+4) = (2*x+4)/(x+5) * (x+5) := by
      symm; exact div_mul_cancel₀ (2 * x + 4) xne
    constructor <;> intro h
    · rw [this, h]; ring
    · rw [h]; field_simp [xne]; ring
  -- 2x+4 = -x^2-3x+10, so x^2+5x+6=0. and it is (x-1)(x+6)=0
  have h3: 2*x+4 = -x^2-3*x+10 ↔ (x-1)*(x+6) = 0 := by
    constructor <;> intro h
    · have: 0 = (2*x+4) - (2*x+4) := by ring
      rw [this]; nth_rw 2 [h]; ring
    · rw [← add_zero 10, ← h]; ring
  -- because x ≠ 1, (x-1)(x+6)=0 leads to x+6=0, therefore x=-6
  have h4: (x-1)*(x+6)=0 ↔ x=-6 := by
    simp
    constructor <;> intro h
    · rcases h with t1 | t6
      · rw [← add_zero 1, ← t1] at hx; simp at hx
      · rw [← add_zero (-6), ← t6]; ring
    · rw [h]; simp
  -- then we can solve the equation and decide x.
  by_cases hhx: x = -5
  · rw [hhx];
    -- when x=-5, zero appears at the denominator. and that's not we want. the bi-condition holds because two sides are both false.
    norm_num
  · push_neg at hhx
    have h5: x+5 ≠ 0 := by
      by_contra! hc; rw [← add_zero (-5), ← hc] at hhx; simp at hhx
    rw [h1, h2 h5, h3, h4]