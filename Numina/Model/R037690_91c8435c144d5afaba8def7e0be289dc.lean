import Mathlib

open Real Set

theorem algebra_111845 {y : ℝ → ℝ} (hy : ∀ x, y x = abs (x - 1) + abs (x - 1)) :
    IsLeast (range y) (y 1) ∧ ¬∃! x, y x = y 1 ∧ ¬∃ n, {x | y x = y 1}.encard = n := by

  have h1 : ∀ x, y x = 2 * |x - 1| := by
    intro x
    rw [hy x]
    ring
  have h2 : y 1 = 0 := by
    rw [h1 1]
    norm_num [abs_of_nonneg]

  constructor
  · -- Show that y 1 is the least element in the range
    constructor
    · -- Show that y 1 is in the range
      use 1
      all_goals simp [h2]
    · -- Show that y 1 is ≤ any other value in the range
      intro r hr
      rcases hr with ⟨x, hx⟩
      rw [show y 1 = (0 : ℝ) by linarith [h2]] at *
      rw [h1 x] at hx
      have h4 : 2 * |x - 1| ≥ 0 := by
        have h5 : |x - 1| ≥ 0 := abs_nonneg (x - 1)
        nlinarith
      linarith
  · -- Show that `∃! x, y x = y 1 ∧ ¬∃ n, {x | y x = y 1}.encard = n` is false
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h4 : y x = y 1 := by
      tauto
    have h5 : y x = 0 := by
      linarith [h2, h4]
    have h6 : x = 1 := by
      have h7 : y x = 0 := h5
      rw [h1 x] at h7
      have h8 : |x - 1| = 0 := by
        linarith
      have h9 : x - 1 = 0 := by
        rw [abs_eq_zero] at h8
        linarith
      linarith
    have h7 : ¬∃ n, {x | y x = y 1}.encard = n := by
      tauto
    have h8 : ∃ n, {x | y x = y 1}.encard = n := by
      use 1
      have h10 : {x | y x = y 1} = {1} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · -- Assume $y x = y 1$, show $x = 1$
          intro h_eq
          have h3 : y x = y 1 := by linarith
          have h4 : y x = 0 := by
            linarith [h2, h3]
          rw [h1 x] at h4
          have h5 : |x - 1| = 0 := by
            linarith
          have h6 : x - 1 = 0 := by
            rw [abs_eq_zero] at h5
            linarith
          linarith
        · -- Assume x = 1, show y x = y 1
          intro h_eq
          rw [h_eq]
          all_goals
            linarith [h2]
      rw [h10]
      simp [Set.encard_singleton]
    contradiction