import Mathlib

theorem number_theory_149524 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) :
    {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p}.encard ≤ 1275 := by
  have h1 : {p | ∃ i j, p = r i * ir j ∧ ¬Irrational p} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, j, hp_eq, h_p_not_irr⟩
    have h_p_not_irr : ¬ Irrational p := by simpa using h_p_not_irr
    rw [hp_eq] at h_p_not_irr
    have h1 : Irrational (r i * (ir j) ) := by
      have h2 : Irrational (ir j) := hriq j
      have h3 : ¬ (r i) = 0 := by
        have h0 : (r i) ≠ 0 := hr i
        exact_mod_cast h0
      have h4 : Irrational ((ir j) ) := h2
      have h5 : Irrational ((r i * (ir j) ) ) := by
        rw [show r i * (ir j) = (ir j) * (r i) by ring]
        apply Irrational.mul_rat
        exact h4
        all_goals norm_cast at h3 ⊢
        all_goals tauto
      exact h5
    have h3 : ¬ Irrational (r i * (ir j) ) := by
      simpa using h_p_not_irr
    contradiction
  rw [h1]
  simp