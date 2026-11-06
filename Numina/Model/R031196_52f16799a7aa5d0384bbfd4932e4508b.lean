import Mathlib

theorem algebra_9311 (a : ℝ) :
    {x | x^2 - 4 * x + a^2 ≤ 0} = ∅ ↔ a < -2 ∨ a > 2 := by 
  simp [Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
  constructor 
  · -- Assume that the solution set is empty, and prove $a < -2 \vee a > 2$.
    intro h 
    have h1 : ∀ x : ℝ, x^2 - 4 * x + a^2 > 0 := by 
      intro x 
      specialize h x 
      simpa using h 
    -- For $a$ algebra, let's check at $x = 2$, where minimum occurs.
    have h2 := h1 2 
    have h3 : a^2 > 4 := by 
      nlinarith [h2] 
    -- Now, derive the inequalities on a.
    by_cases h4 : a > 0 
    · -- If $a > 0$
      have ha : a > 2 := by
        nlinarith [h3, h4]
      right 
      exact ha 
    · -- If not $a > 0$, so $a ≤ 0$
      have ha0 : a ≤ 0 := by
        nlinarith [show ¬ a > (0 : ℝ) by simpa using h4]
      have ha : a < -2 := by
        nlinarith [h3, ha0]
      left 
      exact ha 
  · -- Now prove the converse: if $a < -2 \vee a > 2$, then the solution set is empty.
    rintro (h | h)
    · -- Assume $a < -2$
      intro x 
      have h3 : a^2 > 4 := by
        nlinarith [sq_nonneg (a + 2), h] 
      have : (x - 2) ^ 2 + a^2 - 4 > 0 := by 
        nlinarith [sq_nonneg (x - 2), h3] 
      nlinarith 
    · -- Assume $a > 2$
      intro x 
      have h3 : a^2 > 4 := by
        nlinarith [sq_nonneg (a - 2), h] 
      have : (x - 2) ^ 2 + a^2 - 4 > 0 := by 
        nlinarith [sq_nonneg (x - 2), h3] 
      nlinarith