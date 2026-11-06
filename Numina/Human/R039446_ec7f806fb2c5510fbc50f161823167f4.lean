import Mathlib

/- Find the largest constant $C$ so that
\[x^2 + y^2 + 1 \ge C(x + y)\]for all real numbers $x$ and $y.$ -/
theorem algebra_14796: IsGreatest {C:ℝ | ∀x y:ℝ, x^2+y^2+1 ≥ C*(x+y)} √2 := by
  rw [IsGreatest, upperBounds]; simp
  constructor
  -- first, we verify √2 satifies given conditions.
  intro x y
  -- notice that to prove √2(x+y) ≤ x^2+y^2+1, is same to prove x^2-√2x+1/2 + y^2 -√2y +1/2 ≥ 0, which is (x-1/√2)^2 + (y-1/√2)^2, and obviously nonnegative.
  have h1: x^2 + y^2 + 1 ≥ √2 * (x+y) :=
  calc
    x^2+y^2+1 = (x^2-√2*x+1/2) + (y^2-√2*y+1/2) + √2 * (x+y) := by ring
    _= (x-√2/2)^2 + (y-√2/2)^2 + √2 * (x+y) := by
      have: √2^2 * (1/4) = 1/2 := by norm_num
      have ht1: (x^2-√2*x+1/2) = (x-√2/2)^2 := by
        ring_nf; rw [← this]; ring
      have ht2: (y^2-√2*y+1/2) = (y-√2/2)^2 := by
        ring_nf; rw [← this]; ring
      rw [ht1, ht2]
    _ ≥ √2 * (x+y) := by
      have ht1 := sq_nonneg (x-√2/2)
      have ht2 := sq_nonneg (y-√2/2)
      linarith [ht1, ht2]
  exact h1
  -- the other direction, we show if x^2+y^2+1 ≥ C(x+y), then C ≤ √2.
  intro C h
  -- in the first direction, we rewrite x^2-√2x in the form of (x-1/√2)^2-1/2, and this suggests that when x=y=C/2, C(x+y) = x^2+y^2+1. so we choose such x and y, that left side is closest to the right side.
  rcases h (C/2) (C/2) with ineq'
  have hleft: C * (C / 2 + C / 2) = C^2 := by ring
  have hright: (C/2)^2 + (C/2)^2 + 1 = C^2 / 2 + 1 := by ring
  -- so we have C^2/2 ≤ 1, therefore C ≤ √2.
  have ineq: C^2/2 ≤ 1 := by
    rw [hleft,hright] at ineq'
    linarith [ineq']
  by_contra! hc
  have: C^2 / 2 > 1 := by
    have ht1: C^2 > (√2)^2 := by
      rw [pow_two,pow_two]
      have tt1: 0 < √2 := by norm_num
      have tt2: 0 < C := by linarith [hc,tt1]
      apply mul_lt_mul_of_pos' hc hc tt1 tt2
    have ht2: (√2)^2 = 2 := by norm_num
    rw [ht2] at ht1
    linarith [ht1]
  linarith [ineq, this]
  