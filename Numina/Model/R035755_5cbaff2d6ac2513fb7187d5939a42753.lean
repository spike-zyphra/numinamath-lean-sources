import Mathlib

theorem algebra_606142 : {f : ℝ → ℝ | ∀ x y, f (x ^ 2 * y) = f (x * y) + y * f (f x + y)} =
    {fun _ => 0} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if $f$ satisfies the equation, then $f = 0$.
    intro h
    have h1 : ∀ y, y * f (f 0 + y) = 0 := by
      intro y
      specialize h 0 y
      simp at h
      simpa using h

    have h3 : f 0 = 0 := by
      have eq1 := h1 (-f 0)
      simp at eq1
      exact eq1

    have h4 : ∀ y, y * f y = 0 := by
      intro y
      have eq1 := h1 (y - f 0)
      rw [h3] at eq1
      simp at eq1
      simpa using eq1

    funext y
    by_cases hy : y = 0
    · -- If y = 0, then f(0) = 0 by h3
      rw [hy]
      all_goals try simp [h3]
    · -- If y ≠ 0, then from y * f(y) = 0, we get f(y) = 0
      have hy' : y ≠ 0 := by
        intro h
        apply hy
        linarith
      have eq1 : f y = 0 := by
        apply (mul_left_inj' hy').mp
        linarith [h4 y]
      simpa using eq1
  · -- Now prove the converse: if f = 0, then it satisfies the equation.
    intro h x y
    simp [h]
    <;> linarith