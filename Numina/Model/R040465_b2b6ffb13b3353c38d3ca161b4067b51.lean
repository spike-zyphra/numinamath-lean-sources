import Mathlib

open Real

theorem algebra_10261 (f : ℝ → ℤ) (hf : ∀ x, x > -2 → f x = ⌈1 / (x + 2)⌉) (hf' : ∀ x, x < -2 → f x = ⌊1 / (x + 2)⌋) :
    {0} = {n | ¬ ∃ x ≠ -2, f x = n} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n = 0
    intro hn
    rw [hn]
    intro h
    rcases h with ⟨x, hx1, hx2⟩
    by_cases h1 : x > -2
    · -- If x > -2, then f x = ⌈1 / (x + 2)⌉.
      have hx2' : f x = ⌈1 / (x + 2)⌉ := hf x h1
      rw [hx2'] at hx2
      have h3 : (1 / (x + 2) : ℝ) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith
      have h4 : ⌈1 / (x + 2)⌉ ≥ 1 := by
        have h3' : (1 / (x + 2) : ℝ) > 0 := h3
        have h6 : ⌈1 / (x + 2)⌉ ≥ 1 := by
          by_contra h
          push_neg at h
          have h8 : ⌈1 / (x + 2)⌉ ≤ 0 := by omega
          have h9 : (1 / (x + 2) : ℝ) ≤ (0 : ℝ) := by
            have h12 : (1 / (x + 2) : ℝ) ≤ (⌈1 / (x + 2)⌉ : ℝ) := by
              exact Int.le_ceil (1 / (x + 2) : ℝ)
            have h13 : (⌈1 / (x + 2)⌉ : ℝ) ≤ (0 : ℝ) := by
              exact_mod_cast (show ⌈1 / (x + 2)⌉ ≤ 0 by omega)
            linarith
          linarith
        linarith
      omega
    · -- x ≤ -2
      have h14 : x ≤ -2 := by linarith
      have h10 : x < -2 := by
        by_contra h
        push_neg at h
        have h20 : x = -2 := by linarith
        tauto
      have hx2' : f x = ⌊1 / (x + 2)⌋ := hf' x h10
      rw [hx2'] at hx2
      have h11 : (1 / (x + 2) : ℝ) < (0 : ℝ) := by
        apply div_neg_of_pos_of_neg
        norm_num
        all_goals linarith
      have h12 : ⌊1 / (x + 2)⌋ ≤ -1 := by
        have h11' : (1 / (x + 2) : ℝ) < (0 : ℝ) := h11
        have h14 : ⌊1 / (x + 2)⌋ ≤ -1 := by
          by_contra h
          push_neg at h
          have h15 : ⌊1 / (x + 2)⌋ ≥ 0 := by omega
          have h16 : (1 / (x + 2) : ℝ) ≥ (0 : ℝ) := by
            have h110 : (⌊1 / (x + 2)⌋ : ℝ) ≤ (1 / (x + 2) : ℝ) := by
              exact Int.floor_le (1 / (x + 2) : ℝ)
            have h111 : (⌊1 / (x + 2)⌋ : ℝ) ≥ (0 : ℝ) := by
              exact_mod_cast show ⌊1 / (x + 2)⌋ ≥ (0 : ℤ) by omega
            linarith
          linarith
        linarith
      omega
  · -- Assume 0 ∈ {n | ¬ ∃ x ≠ -2, f x = n}
    intro h
    have h0 : n = 0 := by
      by_contra h6
      have h14 : n ≠ 0 := by
        omega
      have h16 : ¬∃ x ≠ -2, f x = n := by
        simpa using h
      by_cases h17 : n > 0
      · -- n > 0
        have h11 : ∃ x ≠ -2, f x = n := by
          use (1 / (↑n : ℝ) - 2)
          constructor
          · -- Show (1/n - 2) ≠ -2
            by_contra h
            have h0 : (1 / (↑n : ℝ) - 2 : ℝ) = -2 := by
              linarith
            have h1 : (1 / (↑n : ℝ) : ℝ) = 0 := by
              nlinarith
            have h2 : (↑n : ℝ) ≠ 0 := by
              positivity
            field_simp at h1
          · -- Show f ((1/n - 2)) = n
            have h21 : (1 / (↑n : ℝ) - 2 : ℝ) > -2 := by
              have h23 : (1 / (↑n : ℝ) : ℝ) > 0 := by
                apply div_pos
                norm_num
                positivity
              linarith
            have h00 : f ((1 / (↑n : ℝ) - 2 : ℝ)) = ⌈1 / ((1 / (↑n : ℝ) - 2 + 2) : ℝ)⌉ := hf ((1 / (↑n : ℝ) - 2) : ℝ) (by linarith)
            have h4 : ((1 / (↑n : ℝ) - 2 : ℝ) + 2 : ℝ) = ((1 / (↑n : ℝ) : ℝ)) := by ring
            rw [h4] at h00
            have h004 : ⌈1 / ((1 / (↑n : ℝ) : ℝ) : ℝ)⌉ = (↑n : ℤ) := by
              simp
            rw [h004] at h00
            all_goals
              simpa using h00
        tauto
      · -- n ≤ 0
        have h18 : n ≤ 0 := by omega
        by_cases h19 : n < 0
        · -- n < 0
          have h11 : ∃ x ≠ -2, f x = n := by
            use (1 / (↑n : ℝ) - 2)
            constructor
            · -- Show (1/n - 2) ≠ -2
              by_contra h
              have h0 : (1 / (↑n : ℝ) - 2 : ℝ) = -2 := by
                linarith
              have h1 : (1 / (↑n : ℝ) : ℝ) = 0 := by
                nlinarith
              have h2 : (↑n : ℝ) ≠ 0 := by
                have h6 : (↑n : ℝ) < (0 : ℝ) := by
                  exact_mod_cast (show n < (0 : ℤ) by linarith)
                nlinarith
              field_simp at h1
            · -- Show f ((1/n - 2)) = n
              have h115 : (1 / (↑n : ℝ) - 2 : ℝ) < -2 := by
                have h24 : (1 / (↑n : ℝ) : ℝ) < 0 := by
                  apply div_neg_of_pos_of_neg
                  norm_num
                  have h23 : (↑n : ℝ) < (0 : ℝ) := by exact_mod_cast (show n < 0 by linarith)
                  nlinarith
                nlinarith
              have h00 : f ((1 / (↑n : ℝ) - 2 : ℝ)) = ⌊1 / ((1 / (↑n : ℝ) - 2 + 2) : ℝ)⌋ := hf' ((1 / (↑n : ℝ) - 2) : ℝ) (by linarith)
              have h4 : ((1 / (↑n : ℝ) - 2 : ℝ) + 2 : ℝ) = ((1 / (↑n : ℝ) : ℝ)) := by ring
              rw [h4] at h00
              have h004 : ⌊1 / ((1 / (↑n : ℝ) : ℝ) : ℝ)⌋ = (↑n : ℤ) := by
                simp
              rw [h004] at h00
              all_goals
                simpa using h00
          tauto
        · -- n ≥ 0
          have h190 : n ≥ 0 := by omega
          omega
    omega