import Mathlib

open Filter

/- 3. Let real numbers $x_{1}, x_{2}, x_{3}, y_{1}, y_{2}, y_{3}$ satisfy $x_{1}^{2}+x_{2}^{2}+x_{3}^{2} \leqslant 1$, prove:

$$

\left(x_{1} y_{1}+x_{2} y_{2}+x_{3} y_{3}-1\right)^{2} \geqslant\left(x_{1}^{2}+x_{2}^{2}+x_{3}^{2}-1\right) \cdot\left(y_{1}^{2}+y_{2}^{2}+y_{3}^{2}-1\right) .

$$
 -/
theorem inequalities_180447 (x y : Fin 3 → ℝ)
    (h : ∑ i, (x i)^2 ≤ 1) :
    (∑ i, x i * y i - 1)^2 ≥ (∑ i, (x i)^2 - 1) * (∑ i, (y i)^2 - 1) := by
  -- define a, b, c as we'll write quadratic expression
  let a := ∑ i, (x i)^2 - 1
  let c := ∑ i, (y i)^2 - 1
  let b := -2 * (∑ i, x i * y i - 1)
  let f (x : ℝ) := a * (x * x) + b * x + c
  let g (x : ℝ) := (a * x + b) * x + c
  -- two cases a < 0 or a = 0
  obtain ha | ha := lt_or_eq_of_le h
  -- if a < 0 we'll use intermediate value theorem on the quadratic expression, so first prove continuity
  . have hf_cont : Continuous f := by fun_prop
    -- next prove there is a nonnegative value by showing f 1 is nonnegative
    have hf_nonpos : ∃ p, 0 ≤ f p := by
      use 1
      -- simplifying the expression, we see f p is sum of 3 squares which is nonnegative
      convert_to 0 ≤ ∑ i, (x i - y i) ^ 2
      . simp [f, a, b, c]
        ring_nf
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_congr (rfl)]
        rintro i hi
        ring
      apply Finset.sum_nonneg
      rintro i hi
      positivity
    -- next we'll show g tends to -∞ as x tends ∞
    have hf_bot : Tendsto g atTop atBot := by
      simp [g]
      apply tendsto_atBot_add_const_right
      apply Tendsto.atBot_mul_atTop
      . apply tendsto_atBot_add_const_right
        apply Tendsto.const_mul_atTop_of_neg
        . simp [a]
          exact ha
        . exact tendsto_id
      . exact tendsto_id
    -- now we'll show there is a p so that f p ≤ 0
    have hf_nonneg : ∃ p, f p ≤ 0 := by
      -- we'll show that as g p ≤ 0 as both are same
      convert_to ∃ p, g p ≤ 0
      . ext x
        simp [f, g]
        constructor <;> rintro h <;> linarith
      -- next we'll use g's -∞ limit to show there is a x so that g x ≤ 0
      apply Eventually.exists (f := atTop)
      exact Tendsto.eventually_le_atBot hf_bot 0
    -- so by intermeidate value theorem there is a real root of f
    have hf_zero := mem_range_of_exists_le_of_exists_ge hf_cont hf_nonneg hf_nonpos
    -- there for discriminant is a square
    simp [f] at hf_zero
    obtain ⟨p, hp⟩ := hf_zero
    have hd := discrim_eq_sq_of_quadratic_eq_zero hp
    -- then the discriminant is nonnegative
    replace hd : 0 ≤ discrim a b c := by
      rw [hd]
      positivity
    -- from that we get our inequality
    simp [discrim, a, b, c] at hd
    linarith
  -- if a = 0, then the inequality turns to positivity of a square
  . rw [ha]
    simp
    positivity