import Mathlib

theorem number_theory_203820 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) :
    {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p}.encard ≤ 1250 := by

  have h1 : ∀ i j, Irrational (r i * ir j) := by 
    intro i j
    have hrne : (r i : ℝ) ≠ 0 := by 
      have h1 : r i ≠ 0 := hr i
      exact_mod_cast h1
    have h2 : Irrational (ir j) := hriq j
    have h3 : Irrational ((r i : ℝ) * (ir j : ℝ)) := by
      have h4 : Irrational (ir j) := h2
      rw [show ((r i : ℝ) * (ir j : ℝ)) = (ir j) * (r i : ℝ) by ring]
      apply Irrational.mul_rat
      exact h4
      all_goals norm_cast at hrne ⊢
    exact h3

  have h2 : {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    rintro ⟨i, j, hp_eq, hp_not_irrational⟩
    have h3 : Irrational (r i * ir j) := h1 i j
    rw [hp_eq] at hp_not_irrational
    contradiction
  
  rw [h2]
  simp