import Mathlib

open Real Set
open scoped Real

theorem algebra_164470 (m : ℝ) :
  {x | cos x ^ 2 + sin x + m = 0} ≠ ∅ ↔ -5 / 4 ≤ m ∧ m ≤ 1 := by
  have h1 : {x | cos x ^ 2 + sin x + m = 0} ≠ ∅ ↔ ∃ x, cos x ^ 2 + sin x + m = 0 := by
    simp [Set.ext_iff, Set.mem_setOf_eq, Set.eq_empty_iff_forall_not_mem]
    <;> tauto
  rw [h1]
  constructor
  · -- Assume there exists an x such that cos x ^ 2 + sin x + m = 0, prove -5/4 ≤ m ∧ m ≤ 1
    intro h
    rcases h with ⟨x, hx⟩
    have h2 : cos x ^ 2 + sin x + m = 0 := hx
    have h3 : cos x ^ 2 = 1 - sin x ^ 2 := by
      rw [←Real.cos_sq_add_sin_sq x]
      linarith
    rw [h3] at h2
    have h4 : sin x ^ 2 - sin x - 1 - m = 0 := by linarith
    have h5 : -1 ≤ sin x ∧ sin x ≤ 1 := by
      constructor
      · exact neg_one_le_sin x
      · exact sin_le_one x
    have h6 : -5 / 4 ≤ m := by
      nlinarith [sq_nonneg (sin x - 1 / 2)]
    have h7 : m ≤ 1 := by
      nlinarith [sq_nonneg (sin x + 1)]
    constructor
    · linarith
    · linarith
  · -- Assume -5/4 ≤ m ∧ m ≤ 1, prove ∃ x, cos x ^ 2 + sin x + m = 0
    rintro ⟨h1, h2⟩
    have h3 : -1 ≤ (1 - Real.sqrt (5 + 4 * m)) / 2 ∧ (1 - Real.sqrt (5 + 4 * m)) / 2 ≤ 1 := by
      constructor
      · -- Show that -1 ≤ (1 - Real.sqrt (5 + 4 * m)) / 2
        nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (5 + 4 * m) ≥ 0 by linarith)]
      · -- Show that (1 - Real.sqrt (5 + 4 * m)) / 2 ≤ 1
        nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (5 + 4 * m) ≥ 0 by linarith)]
    have h4 : ∃ x, sin x = (1 - Real.sqrt (5 + 4 * m)) / 2 := by
      use arcsin ((1 - Real.sqrt (5 + 4 * m)) / 2)
      rw [Real.sin_arcsin]
      · linarith [h3.1, h3.2]
      all_goals
        try linarith [h3.1, h3.2]
    rcases h4 with ⟨x, hx⟩
    use x
    have h5 : cos x ^ 2 + sin x + m = 0 := by
      have h6 : cos x ^ 2 = 1 - sin x ^ 2 := by
        rw [←Real.cos_sq_add_sin_sq x]
        nlinarith
      rw [h6, hx]
      nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (5 + 4 * m) ≥ 0 by linarith)]
    linarith