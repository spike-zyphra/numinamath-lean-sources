import Mathlib
open Real

/- For all $x \in (0, +\infty)$, the inequality $(2x - 2a + \ln \frac{x}{a})(-2x^{2} + ax + 5) \leq 0$ always holds. Determine the range of values for the real number $a$. -/
theorem algebra_9441 {a : ℝ} (ha : 0 < a) :
    (∀ x > 0, (2 * x - 2 * a + log (x / a)) * (-2 * x ^ 2 + a * x + 5) ≤ 0) ↔
    a = sqrt 5 := by

  -- The function f(x) := 2x + log(x) is strictly increasing on (0, ∞)
  let f x := 2 * x + log x
  have hf' {x y} (hx : x > 0) (hxy : x < y) : f x < f y := by
    simp [f]
    linarith [log_lt_log hx hxy]

  -- Thus f(x) ≤ f(y) ↔ x ≤ y
  have hf {x y} (hx : x > 0) (hy : y > 0) : f x ≤ f y ↔ x ≤ y := by
    constructor <;> intro h
    . contrapose! h
      exact hf' hy h
    . obtain h | h := eq_or_lt_of_le h
      . rw [h]
      . linarith [hf' hx h]

  -- The term 2 * x - 2 * a + log (x / a) is equal to f(x) - f(a)
  have h1 {x a : ℝ} (hx : x > 0) (ha : 0 < a) : 2 * x - 2 * a + log (x / a) = f x - f a := by
    simp [f, @log_div x a (by linarith) (by linarith)]
    linarith

  -- Some transformations to simplify the goal
  conv =>
    lhs
    intro x hx
    -- Rewrite using h1, and the fact that a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b
    rw [h1 hx ha, mul_nonpos_iff]
    -- Eliminate f using its strict monotonicity
    congr
    . lhs
      rw [sub_nonneg, hf ha hx]
    . lhs
      rw [sub_nonpos, hf hx ha]

  -- Clear all about f
  clear f hf hf' h1
  have h0 : √5^2 = 5 := by simp
  constructor <;> intro h

  -- Split the goal into two
  . -- We derive a = √5 from the hypothesis that the inequality holds for all x > 0
    -- We prove that neither a < √5 nor a > √5 is possible
    by_contra! h2
    obtain h2 | h2 := lt_or_gt_of_ne h2
    . -- If a < √5, set x = (a + √5) / 2 > a
      -- And we can show -2 * x^2 + a * x + 5 > 0, which is equivalent to a < √5
      have h3 : (a + √5) / 2 > 0 := by positivity
      specialize h ((a + √5) / 2) h3
      ring_nf at h

      -- Neither part of the disjunction can hold
      obtain ⟨_, h⟩ | ⟨h, _⟩ := h
      . replace h : a * √5 ≥ √5 * √5 := by linarith
        nlinarith
      . linarith

    . -- If a > √5, set x = (3 * a + 2 * √5) / 5 < a
      -- And we can show -2 * x^2 + a * x + 5 > 0, which is equivalent to (a - √5) * (3 * a + 17 * √5) > 0
      have h3 : (3 * a + 2 * √5) / 5 > 0 := by positivity
      specialize h ((3 * a + 2 * √5) / 5) h3
      ring_nf at h

      -- Neither part of the disjunction can hold
      obtain ⟨h, _⟩ | ⟨_, h⟩ := h
      . linarith
      . replace h : (a - √5) * (3 * a + 17 * √5) ≤ 0 := by linarith
        nlinarith [(by positivity : 3 * a + 17 * √5 > 0)]

  . -- If a = √5, we need to prove that the inequality holds for all x > 0
    -- We first clear all about a
    intro x hx
    rw [h]
    clear a ha h

    -- Rewrite -2 * x ^ 2 + √5 * x + 5 as -(2 * x + √5) * (x - √5)
    have h1 : -2 * x ^ 2 + √5 * x + 5 = -(2 * x + √5) * (x - √5) := by linarith
    rw [h1]

    -- Case analysis on x ≤ √5 ∨ x ≥ √5, both cases are trivial
    obtain h | h := le_total x √5
    . refine Or.inr ⟨h, ?_⟩
      nlinarith
    . refine Or.inl ⟨h, ?_⟩
      have h2 : 2 * x + √5 > 0 := by positivity
      nlinarith
