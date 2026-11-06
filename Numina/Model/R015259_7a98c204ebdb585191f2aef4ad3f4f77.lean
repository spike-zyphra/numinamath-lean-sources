import Mathlib

theorem algebra_139735 {a b : ℤ} (ha : 0 < b) (hb : b < a) :
    a * b - a - b = 1 ↔ (a, b) = (3, 2) := by
  constructor
  · -- Forward direction: Equation implies (3, 2)
    intro h
    have h1 : a * b - a - b = 1 := h
    have h2 : (a - 1) * (b - 1) = 2 := by 
      linarith 
    -- Show b - 1 > 0
    have h4 : 0 < b - 1 := by 
      nlinarith 
      all_goals nlinarith
    -- Show a - 1 divides 2
    have h6 : a - 1 ∣ 2 := by 
      use b - 1 
      linarith 
    -- Show that a - 1 > 0
    have h7 : a - 1 > 0 := by
      nlinarith 
    -- Show that a - 1 ≤ 2
    have h8 : a - 1 ≤ 2 := by 
      apply Int.le_of_dvd (by norm_num) h6 
    -- Case analysis for a - 1
    have h9 : a - 1 = 1 ∨ a - 1 = 2 := by 
      interval_cases h10 : a - 1 <;> omega 
    rcases h9 with h9 | h9 
    · -- Case where a - 1 = 1, leads to a contradiction
      have ha1 : a - 1 = 1 := h9
      have hb1 : b - 1 = 2 := by 
        rw [ha1] at h2 
        nlinarith 
      have ha2 : a = 2 := by linarith
      have hb2 : b = 3 := by linarith 
      linarith 
    · -- Case where a - 1 = 2 
      have ha1 : a - 1 = 2 := h9
      have hb1 : b - 1 = 1 := by 
        rw [ha1] at h2 
        nlinarith 
      have ha2 : a = 3 := by linarith 
      have hb2 : b = 2 := by linarith 
      simp [Prod.ext_iff, ha2, hb2] 
  · -- Reverse direction: (3, 2) implies equation 
    rintro ⟨rfl, rfl⟩
    norm_num