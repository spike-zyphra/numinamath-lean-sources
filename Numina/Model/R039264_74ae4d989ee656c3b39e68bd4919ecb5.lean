import Mathlib

theorem algebra_605246 : {f : ℝ → ℝ | ∀ x y, x ≠ 0 → y ≠ 0 → x * f (x * y) + f (-y) = x * f x} =
    {f : ℝ → ℝ | ∃ c, ∀ x, x ≠ 0 → f x = c + c / x} := by

  ext f
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h : ∀ x y, x ≠ 0 → y ≠ 0 → x * f (x * y) + f (-y) = x * f x} prove {f : ℝ → ℝ | ∃ c, ∀ x, x ≠ 0 → f x = c + c / x}
    intro h

    have h1 : f (-1) = 0 := by
      have eq1 := h (-1) 1 (by norm_num) (by norm_num)
      norm_num at eq1 ⊢
      linarith

    have h2 : ∀ y, y ≠ 0 → f y + f (-y) = f 1 := by
      intro y hy
      have eq1 := h 1 y (by norm_num) hy
      norm_num at eq1 ⊢
      linarith

    use (f 1 / 2)
    intro x hx
    have eq2 := h x (-1) hx (by norm_num)
    have eq4 : f (x * (-1)) = f (-x) := by ring_nf
    rw [eq4] at eq2
    have eq5 : f (-x) = f 1 - f x := by
      specialize h2 x hx
      linarith
    rw [eq5] at eq2
    field_simp [hx] at eq2 ⊢
    nlinarith [eq2]

  · -- Assume (f : ℝ → ℝ) (h : ∃ c, ∀ x, x ≠ 0 → f x = c + c / x)
    rintro ⟨c, hc⟩
    intro x y hx hy
    have h1 : f (x * y) = c + c / (x * y) := by
      apply hc
      apply mul_ne_zero
      exact hx
      exact hy
    have h2 : f x = c + c / x := by
      apply hc
      exact hx
    have h3 : f (-y) = c + c / (-y) := by
      apply hc
      have : (-y) ≠ 0 := by
        intro h'
        apply hy
        linarith
      assumption
    rw [h1, h2, h3]
    field_simp [hx, hy]
    <;> ring