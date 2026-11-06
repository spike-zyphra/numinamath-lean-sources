import Mathlib

theorem algebra_136486 {x : ℝ} (hx : ∃ a b, x = a + b ∧ a = ⌊x⌋ ∧ b = x - ⌊x⌋ ∧ 2 * x + 3 * ⌊x⌋ - 5 * (x - ⌊x⌋) = 4) :
    x = 4 / 3 := by
  rcases hx with ⟨a, b, h1, h2, h3, h4⟩
  have ha_eq : a = (⌊x⌋ : ℝ) := by
    exact_mod_cast h2
  have h_eq : 8 * (a : ℝ) - 3 * x = 4 := by
    have h11 : (2 * x + 3 * (⌊x⌋ : ℝ) - 5 * (x - (⌊x⌋ : ℝ)) = 4) := by 
      simpa using h4
    have h14 : -3 * x + 8 * (⌊x⌋ : ℝ) = 4 := by
      nlinarith 
    have ha_eq : (a : ℝ) = (⌊x⌋ : ℝ) := by 
      exact_mod_cast h2
    rw [show (⌊x⌋ : ℝ) = (a : ℝ) by linarith [ha_eq] ] at h14 
    linarith 
  have h7 : ⌊x⌋ = (1 : ℤ) := by 
    have h11 : ⌊x⌋ ≤ (1 : ℤ) := by 
      by_contra h 
      push_neg at h 
      have h18 : ⌊x⌋ ≥ (2 : ℤ) := by omega 
      have h19 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h18 
      have h20 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x 
      have h25 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x 
      have h_eq' : 8 * (a : ℝ) - 3 * x = (4 : ℝ) := by 
        linarith [h_eq] 
      nlinarith 
    have h12 : ⌊x⌋ ≥ (1 : ℤ) := by 
      by_contra h 
      push_neg at h 
      have h16 : ⌊x⌋ ≤ (0 : ℤ) := by omega 
      have h17 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h16 
      have h20 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x 
      have h25 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x 
      have h_eq' : 8 * (a : ℝ) - 3 * x = (4 : ℝ) := by 
        linarith [h_eq] 
      nlinarith 
    omega 
  have h8 : (a : ℝ) = (1 : ℝ) := by 
    have h9 : a = ⌊x⌋ := h2 
    have h10 : ⌊x⌋ = (1 : ℤ) := h7 
    rw [show ⌊x⌋ = (1 : ℤ) by omega] at h9 
    have h12 : (a : ℝ) = (1 : ℝ) := by 
      exact_mod_cast h9 
    linarith 
  -- Final comoputation 
  linarith [h_eq, h8]
  all_goals linarith 
  all_goals linarith