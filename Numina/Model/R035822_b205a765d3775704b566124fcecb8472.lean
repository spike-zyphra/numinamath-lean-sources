import Mathlib

open Real

theorem algebra_110399 {f : ℝ → ℝ} (hf : ∀ x, f x = x - 2 * ⌊x⌋) : Function.Bijective f := by
  constructor
  · -- Show f is injective
    intro x y hxy
    have h1 : f x = f y := hxy
    rw [hf, hf] at h1
    -- Rewrite the equation
    -- So h1 : x - 2 * ⌊x⌋ = y - 2 * ⌊y⌋
    -- Rearrange to: x - y = 2 * (⌊x⌋ - ⌊y⌋)
    -- This should lead to a contradiction
    have h20 : (x - y : ℝ) = 2 * (↑⌊x⌋ - (↑⌊y⌋ : ℝ)) := by
      linarith
    -- Prove that the assumption hxy forces ⌊x⌋ = ⌊y⌋
    have h30 : ⌊x⌋ = ⌊y⌋ := by
      by_contra h
      push_neg at h
      have h4 : ⌊x⌋ < ⌊y⌋ ∨ ⌊y⌋ < ⌊x⌋ := by omega
      cases h4 with
      | inl h5 =>
        -- Assume ⌊x⌋ < ⌊y⌋
        -- So ⌊y⌋ ≥ ⌊x⌋ + 1
        have h8 : ⌊y⌋ ≥ ⌊x⌋ + 1 := by omega
        -- Coerced to real, this gives
        -- (↑⌊y⌋ : ℝ) ≥ (↑⌊x⌋ + 1 : ℝ)
        have h9 : (↑⌊y⌋ : ℝ) ≥ (↑⌊x⌋ + 1 : ℝ) := by exact_mod_cast h8
        -- From h20, we have
        -- (x - y : ℝ) = 2 * (↑⌊x⌋ - (↑⌊y⌋ : ℝ))
        -- Substitute from h9
        have h10 : (x - y : ℝ) ≤ -2 := by
          nlinarith [h20, h9, show (↑⌊x⌋ : ℝ) ≤ (x : ℝ) by exact Int.floor_le x, show (↑⌊y⌋ : ℝ) ≤ (y : ℝ) by exact Int.floor_le y, show (x : ℝ) < (↑⌊x⌋ + 1 : ℝ) by exact Int.lt_floor_add_one x, show (y : ℝ) < (↑⌊y⌋ + 1 : ℝ) by exact Int.lt_floor_add_one y]
        have h110 : (x - (y : ℝ) : ℝ) ≥ -1 := by
          nlinarith [show (↑⌊y⌋ : ℝ) ≤ (y : ℝ) by exact Int.floor_le y, show (x : ℝ) ≥ (↑⌊x⌋ : ℝ) by exact Int.floor_le x, show (y : ℝ) < (↑⌊y⌋ + 1 : ℝ) by exact Int.lt_floor_add_one y, show (x : ℝ) < (↑⌊x⌋ + 1 : ℝ) by exact Int.lt_floor_add_one x]
        linarith
      | inr h6 =>
        -- Assume ⌊y⌋ < ⌊x⌋
        -- So ⌊x⌋ ≥ ⌊y⌋ + 1
        have h8 : ⌊x⌋ ≥ ⌊y⌋ + 1 := by omega
        -- Coerced to real, this gives
        -- (↑⌊x⌋ : ℝ) ≥ (↑⌊y⌋ + 1 : ℝ)
        have h9 : (↑⌊x⌋ : ℝ) ≥ (↑⌊y⌋ + 1 : ℝ) := by exact_mod_cast h8
        -- From h20, we have
        -- (x - y : ℝ) = 2 * (↑⌊x⌋ - (↑⌊y⌋ : ℝ))
        -- Substitute from h9
        have h10 : (x - (y : ℝ) : ℝ) ≥ 2 := by
          linarith [h20, h9, show (↑⌊x⌋ : ℝ) ≤ (x : ℝ) by exact Int.floor_le x, show (↑⌊y⌋ : ℝ) ≤ (y : ℝ) by exact Int.floor_le y, show (x : ℝ) < (↑⌊x⌋ + 1 : ℝ) by exact Int.lt_floor_add_one x, show (y : ℝ) < (↑⌊y⌋ + 1 : ℝ) by exact Int.lt_floor_add_one y]
        -- From our bounds on x and y
        -- This leads to a contradiction
        have h110 : (x - (y : ℝ) : ℝ) < 2 := by
          nlinarith [show (↑⌊x⌋ : ℝ) ≤ (x : ℝ) by exact Int.floor_le x, show (↑⌊y⌋ : ℝ) ≤ (y : ℝ) by exact Int.floor_le y, show (x : ℝ) < (↑⌊x⌋ + 1 : ℝ) by exact Int.lt_floor_add_one x, show (y : ℝ) < (↑⌊y⌋ + 1 : ℝ) by exact Int.lt_floor_add_one y]
        linarith
    -- With h5 : ⌊x⌋ = ⌊y⌋, substitute to get x = y
    -- From h1 and h5, we can now substitute to get x = y
    have h2 : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast h30
    simp [h2] at h1
    all_goals
      linarith
    all_goals
      linarith
  · -- Show f is surjective
    intro y
    use (y - 2 * ⌊y⌋)
    simp [hf]
    all_goals
      try { norm_num }
      all_goals
        try { 
          have h : ⌊(y - 2 * (⌊y⌋ : ℝ) : ℝ)⌋ = -⌊y⌋ := by
            have h10 : ⌊(y - 2 * (⌊y⌋ : ℝ) : ℝ)⌋ = -⌊y⌋ := by
              have h20 : (y : ℝ) - 2 * (⌊y⌋ : ℝ) = (y - 2 * ⌊y⌋ : ℝ) := by 
                ring_nf
              have h21 : (↑⌊y⌋ : ℝ) ≤ y := by exact Int.floor_le y
              have h22 : y < (↑⌊y⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one y
              -- Use these relations to derive the desired equality
              rw [h20]
              set n := ⌊y⌋
              -- If we calculate:
              -- y - 2n is a real number such that 
              -- -n ≤ y - 2n < -n + 1
              have h30 : (↑n : ℝ) ≤ y := by exact_mod_cast h21
              have h31 : y < (↑n + 1 : ℝ) := by exact_mod_cast h22
              have h40 : (y : ℝ) - 2 * (↑n : ℝ) ≥ (-↑n : ℝ) := by
                nlinarith
              have h41 : (y : ℝ) - 2 * (↑n : ℝ) < (-↑n + 1 : ℝ) := by
                nlinarith
              rw [Int.floor_eq_iff]
              constructor <;> (try norm_num) <;> try { nlinarith }
            exact h10
          rw [h]
          -- Now simplify the right-hand side
          field_simp
          all_goals
            nlinarith
        }
        try { 
          -- Use contradictions based on floor inequalities
          -- e.g., using negative multiples would be outside of our bounds
          norm_num [Int.floor_eq_iff]
          all_goals
            nlinarith
        }