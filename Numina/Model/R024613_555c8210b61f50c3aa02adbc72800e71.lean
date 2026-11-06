import Mathlib

theorem number_theory_203825 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) :
    {p | ∃ i j, p = r i * ir j ∧ ∃ q : ℚ, p = q}.encard ≤ 1275 := by
  have h1 : ∀ i j : Fin 50, Irrational ((r i : ℝ) * (ir j : ℝ)) := by
    intro i j
    have h2 : Irrational (ir j) := hriq j
    have h3 : (r i : ℚ) ≠ (0 : ℚ) := by
      exact hr i
    have h4 : (r i : ℝ) ≠ (0 : ℝ) := by
      exact_mod_cast h3
    have h5 : Irrational ((ir j : ℝ) * ((r i : ℚ) : ℝ)) := by
      apply Irrational.mul_rat
      exact_mod_cast h2
      norm_num
      exact_mod_cast h3
    have h6 : (ir j : ℝ) * ((r i : ℚ) : ℝ) = (r i : ℝ) * (ir j : ℝ) := by
      ring_nf
    rw [h6] at h5
    exact_mod_cast h5
  have h2 : {p | ∃ i j, p = r i * ir j ∧ ∃ q : ℚ, p = q} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    rcases hp with ⟨i, j, hpij, q, hq⟩
    have h1' := h1 i j
    rw [show (r i * ir j : ℝ) = (q : ℝ) by
      rw [show (r i * ir j : ℝ) = (p : ℝ) by
        simp [show (r i * ir j) = (p) by linarith]
        <;> linarith
      ]
      rw [show (p : ℝ) = (q : ℝ) by
        simp [show (p) = (q) by linarith]
        <;> linarith
      ]
    ] at h1'
    norm_num at h1' ⊢
    all_goals
      exfalso
      norm_num at h1' ⊢
      try
        tauto
  rw [h2]
  simp [Set.encard_empty]
  all_goals linarith