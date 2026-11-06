import Mathlib
open Complex ComplexConjugate

/- Suppose $z$ and $w$ are complex numbers such that
\[|z| = |w| = z \overline{w} + \overline{z} w= 1.\]Find the largest possible value of the real part of $z + w.$ -/
theorem algebra_14821 :
  IsGreatest {x : ℝ | ∃ z w : ℂ, (abs z = 1 ∧ abs w = 1 ∧ z * (conj w) + w * (conj z) = 1 ∧ x = (z + w).re)} (√3) := by

  -- Small helper lemmas about complex numbers.
  have conj_eq (r i) : conj ({re := r, im := i} : ℂ) = {re := r, im := -i} := rfl

  have mul_eq (r1 i1 r2 i2) : ({re := r1, im := i1} : ℂ) * {re := r2, im := i2} = {re := r1 * r2 - i1 * i2, im := r1 * i2 + i1 * r2} := rfl

  have add_eq (r1 i1 r2 i2) : ({re := r1, im := i1} : ℂ) + {re := r2, im := i2} = {re := r1 + r2, im := i1 + i2} := rfl

  -- We have two goals:
  -- 1. Show that √3 can be achieved.
  -- 2. Show that no larger value can be achieved.
  constructor

  . -- We set z = √3 / 2 + 1 / 2 i and w = √3 / 2 - 1 / 2 i.
    use {re := √3 / 2, im := 1 / 2}, {re := √3 / 2, im := -1 / 2}
    -- Remove the complex numbers from the goal.
    simp [Complex.abs, Complex.instStarRing, conj_eq, mul_eq, add_eq, -one_div]
    -- Only some goals with concrete real numbers remain.
    refine ⟨?_, ?_, ?_⟩
    . ring_nf
      simp
      norm_num
    . ring_nf
      simp
      norm_num
    . congr 1
      . ring_nf
        simp
        norm_num
      . ring_nf

  . -- We show that no larger value can be achieved.
    -- Suppose z = a + bi and w = c + di.
    rintro x ⟨⟨a, b⟩, ⟨c, d⟩, hz, hw, h, rfl⟩
    -- We have |z|^2 = |w|^2 = 1.
    -- That is, a^2 + b^2 = c^2 + d^2 = 1.
    simp [Complex.abs] at hz hw
    rw [← sq, ← sq] at hz hw

    -- We have z * conj w + w * conj z = 1.
    -- The real part of LHS is 1
    -- The imaginary part of LHS is 0
    simp [conj_eq, mul_eq, add_eq] at h
    simp
    injection h with h1 h2

    -- Rewrite the equation h1.
    replace h1 : 2 * a * c + 2 * b * d = 1 := by
      linarith only [h1]

    -- We have (a + c)^2 + (b + d)^2 = 3 by linear combination of the conditions hz, hw, h1.
    have H : (a + c)^2 + (b + d)^2 = 3 := by
      calc _ = (a^2 + b^2) + (c^2 + d^2) + (2 * a * c + 2 * b * d) := by ring
           _ = 1 + 1 + 1 := by rw [hz, hw, h1]
           _ = 3 := by norm_num

    -- Thus (a + c)^2 ≤ 3 and a + c ≤ √3.
    apply Real.le_sqrt_of_sq_le
    linarith only [H, sq_nonneg (b + d)]
