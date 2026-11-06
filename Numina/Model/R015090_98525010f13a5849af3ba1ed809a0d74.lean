import Mathlib

theorem number_theory_154281 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, ∃! j, r i = j) (hri : ∀ i, ∃! j, ir i = j)
    (hriq : ∀ i, Irrational (ir i)) :
    {i | ∃ j, ∃ q : ℚ, r i + ir j = q}.encard ≤ 1250 := by
  have h1 : {i | ∃ j, ∃ q : ℚ, r i + ir j = q} = ∅ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    -- h : ∃ j, ∃ q, r i + ir j = q
    -- We now rewrite h to `⊢ False` using hypothesis which irrational
    rcases h with ⟨j1, ⟨q, h⟩⟩
    -- get h4 which contradiction with h5 from special identifier which ABK.ADMINISTER
    have h2 := hriq j1
    have h3 : (ir j1 : ℝ) = (q : ℝ) - (r i : ℝ) := by
      have h_eq : (r i : ℝ) + (ir j1 : ℝ) = (q : ℝ) := by
        simpa using h
      linarith 
    -- Show r i + ir j is rational
    -- `h : ↑(r i) + ir j1 = ↑q` implies that `ir j1 = ↑q - ↑(r i)`, which equals `(q - r i).val`
    -- via `linarith` we have `ir j1 = (q - r i).val`.
    -- because `q` and `r i` are rational, `q - r i` is also a rational value.
    have h4 : ∃ r' : ℚ, (ir j1 : ℝ) = (↑r' : ℝ) := by
      use (q - r i)
      norm_num at h3  ⊢
      all_goals
      try { linarith  }
    obtain ⟨r', h_eq1⟩ := h4
    have h6 : ¬ Irrational (ir j1) := by
      rw [show (ir j1 : ℝ) = (↑r' : ℝ) by linarith [h_eq1]]
      simp
    -- Irrational (ir j1)
    -- We now have a contradiction between h2 : Irrational (ir j1) and h6 : ¬ Irrational (ir j1)
    exact absurd h2 h6
  rw [h1]
  simp