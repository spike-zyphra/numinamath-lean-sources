import Mathlib

/- Example 8 Solve the equation
$$
x+\sqrt{x}+\sqrt{x+2}+\sqrt{x^{2}+2 x}=3 .
$$-/
theorem algebra_296788 :
    {x : ℝ | 0 ≤ x ∧ x + Real.sqrt x + Real.sqrt (x + 2) + Real.sqrt (x ^ 2 + 2 * x) = 3} = {1 / 4} := by
  -- Let f(x) = x + √x + √(x + 2) + √(x² + 2x).
  let f : ℝ → ℝ := fun x => x + Real.sqrt x + Real.sqrt (x + 2) + Real.sqrt (x ^ 2 + 2 * x)
  -- Show that f(1 / 4) = 3.
  have h₀ : f (1 / 4) = 3 := by
    -- Simplify the square roots.
    field_simp [f]
    ring_nf
    field_simp 
    rw [show 3 = 2 + 1 by norm_num, pow_add, show (9 : ℝ) = 3 ^ 2 by norm_num, show (36 : ℝ) = 6 ^ 2 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num]
    iterate 3 rw [Real.sqrt_sq (by norm_num)]
    norm_num
  -- Show that f is strictly increasing on its domain.
  have h₁ (x y : ℝ) (hx : 0 ≤ x) (hy : x < y) : f x < f y := by
    simp [f]
    iterate 3 apply add_lt_add
    . exact hy
    . apply Real.sqrt_lt_sqrt hx
      exact hy
    . apply Real.sqrt_lt_sqrt (by positivity)
      simp [hy]
    . apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith
  -- Now return to the original goal.
  ext x
  simp [-one_div]
  constructor
  · -- Forward implication: assume the equation holds, prove x = 1/4.
    rintro ⟨hx, h⟩
    rw [show x + Real.sqrt x + Real.sqrt (x + 2) + Real.sqrt (x ^ 2 + 2 * x) = f x by simp [f]] at h
    -- Assume on the contrary that x < 1 / 4 or x > 1 / 4, then f(x) ≠ 3.
    by_contra!
    apply ne_iff_lt_or_gt.mp at this
    rcases this with (this | this)
    . specialize h₁ x (1 / 4) hx this
      simp_all
    . specialize h₁ (1 / 4) x (by norm_num) this
      simp_all
  · -- Backward implication: assume x = 1/4, prove the equation holds.
    intro hx
    -- Just use the fact proved above that f(1 / 4) = 3.
    refine ⟨by norm_num [hx], ?_⟩
    simp [<-hx, f] at h₀
    exact h₀