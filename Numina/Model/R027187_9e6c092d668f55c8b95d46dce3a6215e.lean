import Mathlib

theorem algebra_199727 {x : ℝ × ℝ} (hx : 2 * ⌊x.1⌋ + x.2 = 3 / 2 ∧ 3 * ⌊x.1⌋ - 2 * x.2 = 4) :
    1 ≤ x.1 ∧ x.1 < 2 ∧ x.2 = -1 / 2 := by
  rcases hx with ⟨h1, h2⟩
  have eq1 : (⌊x.1⌋ : ℝ) = 1 := by
    have eq1 := h1
    have eq2 := h2
    norm_num at eq1 eq2 
    linarith
  have h4 : ⌊x.1⌋ = 1 := by
    exact_mod_cast eq1
  have h5 : 1 ≤ x.1 := by 
    have h6 : ⌊x.1⌋ = 1 := h4
    have h7 : (⌊x.1⌋ : ℝ) ≤ x.1 := by exact Int.floor_le x.1
    have h8 : (⌊x.1⌋ : ℝ) = 1 := by exact_mod_cast h6
    linarith
  have h6 : x.1 < 2 := by 
    have h7 : ⌊x.1⌋ = 1 := h4
    have h8 : x.1 < (⌊x.1⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x.1
    have h9 : (⌊x.1⌋ : ℝ) = 1 := by exact_mod_cast h7
    linarith
  have h7 : x.2 = -1 / 2 := by
    have eq1 : (⌊x.1⌋ : ℝ) = 1 := by exact_mod_cast h4
    linarith
  exact ⟨h5, h6, h7⟩