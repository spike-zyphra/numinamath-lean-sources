import Mathlib

theorem number_theory_170620 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) :
    {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p}.encard ≤ 1275 := by
  have h1 : {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    rcases h with ⟨i, j, hp_eq, hpi⟩
    have h2 : Irrational ((r i : ℝ) * (ir j)) := by
      have h3 : Irrational (ir j) := hriq j
      have h4 : (r i : ℝ) ≠ 0 := by
        exact_mod_cast (hr i)
      have h5 : Irrational ((r i : ℝ) * (ir j)) := by
        rw [show (r i : ℝ) * (ir j) = ((r i : ℚ) : ℝ) * (ir j) by simp]
        apply Irrational.rat_mul
        exact h3
        all_goals
          exact_mod_cast (hr i)
      exact h5
    have h6 : Irrational p := by
      rw [hp_eq]
      exact_mod_cast h2
    exfalso
    tauto
  rw [h1]
  simp