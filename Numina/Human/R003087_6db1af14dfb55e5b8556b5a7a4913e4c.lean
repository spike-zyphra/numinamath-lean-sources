import Mathlib

open Real

-- Show that sin (a * x)^2 - cos x + 1 = 0 iff
-- a * x = k * π and x = 2 * l * π for some integer k and l.
lemma lemma_1 {a x : ℝ} :
    sin (a * x) ^ 2 - cos x + 1 = 0 ↔ ∃ k l : ℤ, a * x = k * π ∧ x = 2 * l * π := calc
  -- sin (a * x)^2 - cos x + 1 = 0 iff sin (a * x)^2 = 0 and cos x = 1.
  -- This follows from cos x ≤ 1.
  _ ↔ sin (a * x) ^ 2 = 0 ∧ cos x = 1 := by
    constructor
    · intro h
      suffices cos x ≤ 1 by constructor <;> nlinarith
      apply cos_le_one
    · intro h
      simp [h]
  -- sin (a * x)^2 = 0 iff a * x = k * π for some k ∈ ℤ.
  -- cos x = 1 iff x = 2 * l * π for some l ∈ ℤ.
  _ ↔ ∃ k l : ℤ, a * x = k * π ∧ x = 2 * l * π := by
    rw [pow_eq_zero_iff (by norm_num), sin_eq_zero_iff, cos_eq_one_iff]
    rw [exists_and_exists_comm]
    ac_nf
    tauto

/- ## Task 11/71
For which real numbers $a$ does the equation
$$
\sin ^{2}(a x)-\cos x+1=0
$$
have exactly one solution? -/
theorem algebra_152076 (a : ℝ) :
    (∃! x : ℝ, sin (a * x) ^ 2 - cos x + 1 = 0) ↔ Irrational a := by
  -- lemma_1 implies that sin (a * x)^2 - cos x + 1 = 0 iff
  -- ∃ k l : ℤ, a * x = k * π ∧ x = 2 * l * π.
  simp_rw [lemma_1, ExistsUnique.eq_1]
  constructor
  · intro ⟨x, ⟨k, l, h1, h2⟩, hy⟩
    -- Assume that a * x = k * π, x = 2 * l * π, and a * y = k' * π, y = 2 * l' * π
    -- imply y = x.
    -- Show that a is irrational.
    -- Assume that a is not irrational and show that there exists y ≠ x such that
    -- a * y = k' * π and y = 2 * l * π.
    contrapose! hy
    -- a = q ∈ ℚ.
    simp [Irrational] at hy
    have ⟨q, hq⟩ := hy
    -- q = q.num / q.den.
    rw [Field.ratCast_def] at hq
    subst hq x
    clear hy
    -- Consider two cases: l = 0 or l ≠ 0.
    by_cases hl0 : l = 0
    · -- If l = 0 then take y = 2 * q.den * π.
      subst hl0
      use 2 * q.den * π
      constructor
      · -- Take k' = 2 * q.num and l' = q.den.
        use 2 * q.num, q.den
        -- We get a * y = q.num / q.den * 2 * q.den * π = 2 * q.num * π = k' * π and
        -- y = 2 * l' * π.
        simp
        field_simp [show (q.den : ℝ) ≠ 0 by simp]
        ring
      · -- y = 2 * q.den * π ≠ 2 * 0 * π = 0 (because q.den ≠ 0).
        simp [pi_ne_zero]
    -- Assume now that l ≠ 0.
    -- Take y = 2 * (q.den * 2 * l) * π.
    use 2 * (q.den * 2 * l) * π
    constructor
    · -- Take k' = 2 * (q.num * 2 * l) and l' = q.den * 2 * l.
      use 2 * (q.num * 2 * l), q.den * 2 * l
      -- We get a * y = q.num / q.den * 2 * (q.den * 2 * l) * π
      --    = 2 * (q.num * 2 * l) * π = k' * π and
      -- y = 2 * l' * π.
      simp
      field_simp
      ring
    · -- 2 * (q.den * 2 * l) * π ≠ 2 * l * π is equivalent to
      -- q.den * 2 * l ≠ l.
      simp [pi_ne_zero]
      -- Assume that q.den * 2 * l = l and show that l = 0.
      contrapose! hl0
      -- We have l * (q.den * 2 - 1) = 0.
      replace hl0 : l * (q.den * 2 - 1) = 0 := by
        norm_cast at hl0
        push_cast at hl0
        linear_combination hl0
      rw [mul_eq_zero] at hl0
      -- q.den ≠ 0 so q.den * 2 - 1 ≠ 0. We conclude that l = 0.
      suffices q.den ≠ 0 by omega
      exact q.den_nz
  · -- Assume that a is irrational and show that there exists unique x such that
    -- a * x = k * π and x = 2 * l * π for some k, l ∈ ℤ.
    intro ha
    -- Let x = 0.
    use 0
    simp
    -- We need to show that a * y = k * π, y = 2 * l * π imply that y = 0.
    intro x k eq1 l eq2
    subst x
    -- We get (2 * l) * a = k.
    replace eq1 : ↑(2 * l) * a = k := by
      push_cast
      rw [← mul_right_inj' pi_ne_zero]
      linear_combination eq1
    -- k is rational, so (2 * l) * a is also rational.
    apply_fun Irrational at eq1
    simp only [Int.not_irrational, eq_iff_iff, iff_false, irrational_int_mul_iff] at eq1
    -- a is irrational and (2 * l) * a is rational, so l = 0.
    -- We conclude that y = 2 * l * π = 0.
    simp [ha] at eq1
    simp [eq1]