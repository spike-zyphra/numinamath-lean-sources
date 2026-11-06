import Mathlib

theorem algebra_609736 {x : ℝ} (hx : ⌊x⌋ + x = 2017 ∧ (2017 * x) % 1 = 1 / 2017) :
    x = 3025 + 1 / 2017 := by 
  rcases hx with ⟨h1, h2⟩
  have h3 : ⌊x⌋ ≤ x := by 
    exact Int.floor_le x
  have h4 : x < ⌊x⌋ + 1 := by
    exact Int.lt_floor_add_one x
  have h7 : ⌊x⌋ ≤ 1008 := by 
    by_contra h
    push_neg at h
    have h8 : ⌊x⌋ ≥ 1009 := by omega
    have h9 : (⌊x⌋ : ℝ) ≥ (1009 : ℝ) := by 
      exact_mod_cast h8
    nlinarith
  have h8 : ⌊x⌋ > 1008 := by 
    by_contra h
    push_neg at h
    have h9 : ⌊x⌋ ≤ 1008 := by omega
    have h10 : (⌊x⌋ : ℝ) ≤ (1008 : ℝ) := by
      exact_mod_cast h9
    nlinarith
  have h9 : ⌊x⌋ = 1009 := by
    omega
  have h9' : (⌊x⌋ : ℝ) = (1009 : ℝ) := by
    exact_mod_cast h9
  linarith