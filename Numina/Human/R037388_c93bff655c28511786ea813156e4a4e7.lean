import Mathlib

/- What is the greatest integer value of $b$ such that $-4$ is not in the range of $y=x^2+bx+12$?-/
theorem algebra_16713 (f : ℤ → ℝ → ℝ) (hf : ∀ b, ∀ x, f b x = x ^ 2 + b * x + 12) :
    IsGreatest {b : ℤ | (-4) ∉ Set.range (f b)} 7 := by
  -- We need the lemma that quadratic equation has no real root iff its discriminant is less than 0.
  have hquadratic_ne_zero_iff {a b c : ℝ} (ha : a ≠ 0) :
    (∀ x, a * x ^ 2 + b * x + c ≠ 0) ↔ discrim a b c < 0 := by
    simp only [pow_two, ← mul_assoc]
    constructor
    . intro h
      contrapose! h
      let d := Real.sqrt <| discrim a b c
      have : ∃ s, discrim a b c = s * s := ⟨d, Eq.symm <| Real.mul_self_sqrt h⟩
      convert exists_quadratic_eq_zero ha this using 1
      ext; ring_nf
    intro h
    have : ∀ y, discrim a b c ≠ y ^ 2 := by
      intro y hy
      linarith [hy ▸ sq_nonneg y]
    convert quadratic_ne_zero_of_discrim_ne_sq this using 1
    ring_nf
  simp [Set.range, hf, ← ne_eq]
  constructor
  -- Verify that b=7 is a solution.
  . rw [Set.mem_setOf_eq]
    intro x
    suffices 1 * x ^ 2 + ((7 : ℤ) : ℝ) * x + 16 ≠ 0 by
      contrapose! this
      linear_combination this
    revert x
    -- Suffices to show $7^2 - 4 * 1 * 16 < 0$.
    rw [hquadratic_ne_zero_iff (by norm_num), discrim]
    norm_num
  -- Prove that 7 is the greatest.
  dsimp [upperBounds]
  intro b hx
  replace hx : ∀ x : ℝ, 1 * x ^ 2 + b * x + 16 ≠ 0 := by
    contrapose! hx
    rcases hx with ⟨z, hz⟩
    use z
    linear_combination hz
  -- Since $x^2+bx+16=0$ has no real roots, we have $b^2 - 4 * 1 * 16 < 0$.
  rw [hquadratic_ne_zero_iff (by norm_num), discrim] at hx
  -- Notice that b is an integer, suffices to show $b < 8$.
  suffices b < 8 by omega
  rify
  -- This can be deduced from $b^2 - 4 * 1 * 16 < 0$ easily.
  nlinarith
