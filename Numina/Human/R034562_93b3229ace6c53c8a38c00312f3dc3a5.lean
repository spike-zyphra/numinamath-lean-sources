import Mathlib

/- Let $a,$ $b,$ $c,$ $d,$ $e,$ $f$ be positive real numbers such that $a + b + c + d + e + f = 7.$  Find the minimum value of
\[\frac{1}{a} + \frac{4}{b} + \frac{9}{c} + \frac{16}{d} + \frac{25}{e} + \frac{36}{f}.\] -/
theorem algebra_12557 : IsLeast {x : ℝ | ∃ (a b c d e f : ℝ),
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
  a + b + c + d + e + f = 7 ∧
  x = 1 / a + 4 / b + 9 / c + 16 / d + 25 / e + 36 / f} 63 := by

  -- by Cauchy-Schwarz inequality,
  -- (a+b+...+f) (1/a + 4/b +... + 36/f) ≥ (1+2+..+6)^2
  have ineq {a b c d e f : ℝ} (ha: 0 < a) (hb: 0 < b) (hc: 0 < c)
    (hd: 0 < d) (he: 0 < e) (hf: 0 < f):
    (a+b+c+d+e+f) * (1/a + 4/b + 9/c + 16/d + 25/e + 36/f)
      ≥ (1+2+3+4+5+6)^2 := by
    let s := Finset.range 6
    let ff: ℕ → ℝ := fun i =>
      match i with
      | 0 => √a
      | 1 => √b
      | 2 => √c
      | 3 => √d
      | 4 => √e
      | 5 => √f
      | n+6 => 0
    let gg: ℕ → ℝ := fun i =>
      match i with
      | 0 => 1/√a
      | 1 => 2/√b
      | 2 => 3/√c
      | 3 => 4/√d
      | 4 => 5/√e
      | 5 => 6/√f
      | n+6 => 0

    have h1: ∑ i ∈ s, ff i * gg i = 1+2+3+4+5+6 := by
      simp only [one_div, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, s, ff, gg]
      field_simp

    have h2: ∑ i ∈ s, (ff i)^2 = a+b+c+d+e+f := by
      simp [s, ff, Finset.sum_range_succ,
      Real.sq_sqrt, ha.le, hb.le, hc.le, hd.le, he.le, hf.le]

    have h3: ∑ i ∈ s, (gg i)^2 =
      1 / a + 4 / b + 9 / c + 16 / d + 25 / e + 36 / f := by
      simp only [one_div, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, inv_pow, s, gg, ff]
      field_simp
      ring

    -- use Cauchy-schwarz inequality
    have := Finset.sum_mul_sq_le_sq_mul_sq s ff gg
    rwa [h1, h2, h3] at this

  -- then we claim minimum is (1+2+3+4+5+6)^2/7 = 63
  rw [IsLeast, lowerBounds]
  simp only [exists_and_left, Set.mem_setOf_eq,
  forall_exists_index, and_imp]

  constructor
  · -- reach minimum when equal condition for cauchy-schwarz inequality holds.
    use 1/3
    refine ⟨(by norm_num), ?_⟩
    use 2/3
    refine ⟨(by norm_num), ?_⟩
    use 1
    refine ⟨(by norm_num), ?_⟩
    use 4/3
    refine ⟨(by norm_num), ?_⟩
    use 5/3
    refine ⟨(by norm_num), ?_⟩
    use 2
    norm_num
  · -- prove 63 is a lowerbound using cauchy-schwarz inequality.
    rintro _ a ha b hb c hc d hd e he f hf heq rfl
    specialize ineq ha hb hc hd he hf
    rw [heq] at ineq
    linarith only [ineq]