import Mathlib

theorem algebra_236854 (a b : ℝ) :
    a^2 + b^2 = 25 ∧ 3 * (a + b) - a * b = 15 ↔
    (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 0) ∨ (a = 4 ∧ b = -3) ∨ (a = -3 ∧ b = 4) := by
  constructor
  · -- Assume the equations hold, and find the pairs
    rintro ⟨h1, h2⟩
    have h3 : (a + b) ^ 2 - 6 * (a + b) + 5 = 0 := by
      nlinarith 
    have h4 : ((a + b) - 5) * ((a + b) - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- case where a + b = 5 
      have h3 : a + b = 5 := by linarith 
      have h4 : a * b = 0 := by
        nlinarith [h3, h2] 
      cases' (mul_eq_zero.mp h4) with ha hb
      · -- case where a = 0 
        have ha2 : a = 0 := ha 
        have hb2 : b = 5 := by linarith [h3, ha2]
        left
        exact ⟨ha2, hb2⟩
      · -- case where b = 0 
        have hb2 : b = 0 := hb 
        have ha2 : a = 5 := by linarith [h3, hb2]
        right 
        left 
        exact ⟨ha2, hb2⟩
    · -- case where a + b = 1 
      have h3 : a + b = 1 := by linarith 
      have h4 : a * b = -12 := by 
        nlinarith [h3, h2] 
      have h8 : (a - 4) * (a + 3) = 0 := by
        nlinarith [h3, h4] 
      cases' (mul_eq_zero.mp h8) with ha4 ha3 
      · -- case where a = 4 
        have ha4' : a = 4 := by linarith 
        have hb2 : b = -3 := by linarith [h3, ha4']
        right 
        right 
        left 
        exact ⟨ha4', hb2⟩ 
      · -- case where a = -3 
        have ha3' : a = -3 := by linarith 
        have hb2 : b = 4 := by linarith [h3, ha3']
        right 
        right 
        right 
        exact ⟨ha3', hb2⟩ 
  · -- Now prove the reverse direction
    rintro (h | h | h | h)
    · -- Case (0, 5)
      rcases h with ⟨ha, hb⟩ 
      constructor
      · -- First equation
        nlinarith 
      · -- Second equation
        nlinarith 
    · -- Case (5, 0)
      rcases h with ⟨ha, hb⟩ 
      constructor
      · -- First equation
        nlinarith 
      · -- Second equation
        nlinarith 
    · -- Case (4, -3)
      rcases h with ⟨ha, hb⟩ 
      constructor
      · -- First equation
        nlinarith 
      · -- Second equation
        nlinarith 
    · -- Case (-3, 4)
      rcases h with ⟨ha, hb⟩ 
      constructor
      · -- First equation
        nlinarith 
      · -- Second equation
        nlinarith