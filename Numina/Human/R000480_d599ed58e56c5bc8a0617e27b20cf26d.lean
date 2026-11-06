import Mathlib

/- Find the sum of the squares of the solutions to $$\left| x^2 - x + \frac{1}{2008} \right| = \frac{1}{2008}.$$ -/
theorem algebra_3798
    (s : Finset ℝ)
    (hs : s = {x : ℝ | |x^2 - x + 2008⁻¹| = 2008⁻¹}) :
    ∑ x ∈ s, x ^ 2 = 1003 / 502 := by

  -- If $\left| x^2 - x + \frac{1}{2008} \right| = \frac{1}{2008}$, then either $x^2 - x + \frac{1}{2008} = \frac{1}{2008}$ or $x^2 - x + \frac{1}{2008} = -\frac{1}{2008}$.
  have r0 : ∀ x : ℝ, |x ^ 2 - x + 2008⁻¹| = 2008⁻¹ ↔ x ^ 2 - x + 1 / 2008 = 1 / 2008 ∨ x ^ 2 - x + 2008⁻¹ = - 2008⁻¹ := by
    simp [abs_eq]


  -- In the first case, $x^2 - x = x(x - 1) = 0,$ so $x = 0$ or $x = 1$.
  have r1 : ∀ x : ℝ, x ^ 2 - x + 2008⁻¹ = 2008⁻¹ ↔ x = 0 ∨ x = 1 := by
    simp [show ∀ x : ℝ, x ^ 2 - x = x * (x - 1) by intros; ring, sub_eq_zero]

  -- In the second case, $x^2 - x + \frac{1}{1004} = 0$. Then by Vieta's formulas, $a + b = 1$ and $ab = \frac{1}{1004},$ so $a^2 + b^2 = (a + b)^2 - 2ab = 1 - \frac{1}{502} = \frac{501}{502}.$
  set a : ℝ := 1 / 2 + √ (1 - 251⁻¹) / 2
  set b : ℝ := 1 / 2 - √ (1 - 251⁻¹) / 2
  have : a ^ 2 + b ^ 2 = 501 / 502 := by
    dsimp [a, b]
    ring_nf; field_simp; ring
  have r2 : ∀ x : ℝ, x ^ 2 - x + 2008⁻¹ = -2008⁻¹ ↔ x = a ∨ x = b := by
    intro x
    rw [eq_neg_iff_add_eq_zero,
        show x ^ 2 - x + 2008⁻¹ + 2008⁻¹ = (x - a) * (x - b) by simp [a, b]; ring_nf; field_simp; ring,
        mul_eq_zero, sub_eq_zero, sub_eq_zero]

  simp only [r0, one_div, r1, r2, or_assoc] at hs
  have : {x | x = 0 ∨ x = 1 ∨ x = a ∨ x = b} = {0, 1, a, b} := rfl
  rw [this] at hs
  have : s = {0, 1, a, b} := by
    refine Finset.ext_iff.mpr ?_
    intro x
    constructor
    . intro hx
      have : x ∈ (s : Set ℝ) := by exact hx
      simp [hs] at this
      simp [hs, this]
    . intro hx
      have : x ∈ (s : Set ℝ) := by
        rw [hs]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [hx]
      exact this
  rw [this]

  -- Therefore, the sum of the squares of the solutions is $1 + \frac{501}{502} = \boxed{\frac{1003}{502}}.$
  have : √ 251 > 0 := by apply Real.sqrt_pos_of_pos (by linarith)
  have : √ 250 > 0 := by apply Real.sqrt_pos_of_pos (by linarith)
  have hne : √ 250 ≠ √ 251 := by simp
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  any_goals dsimp [a, b]
  . ring_nf
    field_simp
    ring_nf
  . ring_nf
    field_simp
    linarith
  . ring_nf
    field_simp
    ring_nf
    rw [mul_two]
    constructor
    . apply (add_ne_add_right √251).mpr
      simp
    . by_contra h_contra
      apply_fun fun x => x - √ 251 at h_contra
      ring_nf at h_contra
      linarith
  . ring_nf
    field_simp
    ring_nf
    constructor
    . linarith
    . by_contra!
      have := eq_of_sub_eq_zero (this.symm)
      exact hne this.symm