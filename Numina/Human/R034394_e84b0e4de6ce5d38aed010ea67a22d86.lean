import Mathlib

/- Let $a$ and $b$ be positive real numbers such that $a + 2b = 1.$  Find the minimum value of
\[\frac{1}{a} + \frac{1}{b}.\] -/
theorem algebra_12712 {f:ℝ → ℝ → ℝ}
    (hf: f = fun a b => 1/a + 1/b) :
    IsLeast {x| ∃a b:ℝ, (x = (f a b) ∧  0 < a ∧ 0 < b ∧ a+2*b=1)} (3+2*√2) := by
  -- for a+2b=1 and 1/a+1/b, multiply a+2b to 1/a+1/b, and we will have a form of 2*b/a+a/b+...
  -- and if we view b/a=x, a/b = 1/x, then following lemma is quite useful. so we prove it first.
  have lemma_ineq(a x:ℝ)(posa: 0 < a)(posx: 0 < x): a*x+1/x ≥ 2*√a := by
    -- multiply both sides by x, ax^2 - 2√ax+1 = (√ax-1)^2 ≥ 0
    have ht1: a*x^2 +1 - 2*√a*x ≥ 0 := by
      have: a*x^2+1-2*√a*x = (√a*x-1)^2 := by
        have: a = √a^2 := by
          have: 0 ≤ a := le_of_lt posa
          symm
          exact Real.sq_sqrt this
        nth_rw 1 [this]; ring
      rw [this]
      exact sq_nonneg (√a * x - 1)
    have ht2: a*x^2+1-2*√a*x = ((a*x+1/x)-2*√a)*x := by
      have: 1/x*x=1 := by
        have: x ≠ 0 := by linarith [posx]
        exact one_div_mul_cancel this
      rw [sub_mul, add_mul, this, pow_two, ← mul_assoc]
    rw [ht2] at ht1
    have ht3: a*x+1/x-2*√a ≥ 0 := by
      exact (mul_nonneg_iff_of_pos_right posx).mp ht1
    exact sub_nonneg.mp ht3
  -- equipped with that lemma, we move on.
  rw [IsLeast, lowerBounds, hf]
  constructor <;> simp
  -- in this direction, we verify 3+2√2 is a possible value.
  -- remember that during proving the inequality, we write those expression in a square form, and square is nonnegative. obviously, for expression in forms of (a-b)^2, attains minimum when a=b. so here minimum is taken when √2x=1, or x = 1/√2, b=a/√2. combine with a+2b =1,
  -- we solve b=(2-√2)/2, a = √2-1. so we use these values.
  use (√2-1)
  use (2-√2)/2
  have h1: 1 < √2 := by
    have ht1: 0 < (2:ℝ) := by norm_num
    have ht2: (1:ℝ) = √1 := by norm_num
    rw [ht2]
    apply (Real.sqrt_lt_sqrt_iff_of_pos ht1).mpr
    norm_num
  have h2: 0 < √2-1 := by linarith [h1]
  have h3: (2:ℝ) = √2^2 := by norm_num
  have h4: (2-√2) = √2 * (√2-1) := by
    ring_nf; simp [← h3]; ring
  have h5: (2-√2)/2 = (√2-1)/√2 := by
    field_simp; ring_nf
    simp; ring
  have h6: 3+2*√2 = (√2-1)⁻¹+((2-√2)/2)⁻¹ := by
    field_simp
    ring_nf
    simp [← h3, h4];
    field_simp; ring_nf
    simp [← h3]
    rw [pow_three, ← pow_two, ← h3]; ring
  have h7: 0 < (2-√2)/2 := by
    rw [h5]
    have: 0 < √2 := by norm_num
    exact div_pos h2 this
  have h8: √2-1+2*((2-√2)/2)=1 := by
    rw [← mul_div_assoc, mul_comm, mul_div_assoc]; simp; ring
  exact ⟨h6,h2,h7,h8⟩
  -- next, we prove the expression ≥ 3+2√2. we will use the cauchy_schwarz like inequality in this direction.
  intro y a b hy posa posb hab
  let x := b/a
  have x_def: x = b/a := rfl
  have h1: a⁻¹+b⁻¹ = 2*x+1/x + 3 := by
    rw [← mul_one (a⁻¹+b⁻¹)]
    nth_rw 1 [← hab]
    rw [x_def]; field_simp; ring
  rw [hy, h1]
  -- now, it suffices to prove 2x+1/x+3 ≥ 3+2√2, and for 2x+1/x form, we already found an inequality to deal with.
  have xpos: 0 < x := by
    rw [x_def]
    exact div_pos posb posa
  have pos2: 0 < (2:ℝ) := by norm_num
  have h2 := lemma_ineq 2 x pos2 xpos
  linarith [h2]