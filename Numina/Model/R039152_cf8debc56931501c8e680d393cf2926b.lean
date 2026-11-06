import Mathlib

theorem calculus_22448 (k : ℝ) :
    {t : ℝ | ∃ s : ℝ, (4 + 5 * t) = 8 - 15 * s ∧ (-1 + 2 * t) = k - 6 * s}.Infinite ↔
    k = 3 / 5 := by
  constructor
  · -- Assume the solution set is infinite, prove k = 3/5.
    intro h
    by_contra hk
    push_neg at hk
    have h1 : {t : ℝ | ∃ s : ℝ, (4 + 5 * t) = 8 - 15 * s ∧ (-1 + 2 * t) = k - 6 * s} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rcases h with ⟨s, h1, h2⟩
      have eq1 : 5 * t + 15 * s = 4 := by linarith
      have eq2 : 2 * t + 6 * s = k + 1 := by linarith
      have eq3 : 10 * t + 30 * s = 8 := by
        linarith [eq1]
      have eq4 : 10 * t + 30 * s = 5 * k + 5 := by
        linarith [eq2]
      -- So 8 = 5k + 5 => 3 = 5k => k = 3/5
      have eq5 : 5 * k + 5 = 8 := by
        linarith
      have hk1 : k = 3 / 5 := by
        linarith
      contradiction
    rw [h1] at h
    simp at h
  · -- Assume k = 3/5, prove the solution set is infinite
    intro hk
    rw [hk]
    apply Set.infinite_of_injective_forall_mem (f := fun (n : ℕ) => (4 / 5 - 3 * (↑n : ℝ)))
    · -- Show f is injective
      intro n m h
      simp at h
      linarith
    · -- Show all members are in the set
      intro n
      use (↑n : ℝ)
      constructor
      · -- Check first equation
        ring
      · -- Check second equation
        ring