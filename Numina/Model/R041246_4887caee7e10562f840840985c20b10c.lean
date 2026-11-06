import Mathlib

theorem algebra_295359 (a b c : ℝ) :
    a^2 + b = c^2 ∧ b^2 + c = a^2 ∧ c^2 + a = b^2 ↔
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = -1) ∨
    (a = -1 ∧ b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = -1 ∧ c = 0) := by
  constructor
  · -- Assume the three equations hold, derive the four solutions.
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : a + b + c = 0 := by
      nlinarith
    have hc : c = -a - b := by linarith
    rw [hc] at h₁ h₂ h₃
    have eq1 : b * (b + 2 * a - 1) = 0 := by 
      nlinarith
    have eq2 : (b + a) * (b - a - 1) = 0 := by 
      nlinarith
    have eq3 : a * (a + 2 * b + 1) = 0 := by
      nlinarith
    by_cases ha1 : a = 0
    · -- If a = 0
      have ha1' : a = 0 := ha1
      have eq1' : b * (b - 1) = 0 := by 
        rw [ha1'] at eq1
        linarith
      cases' (mul_eq_zero.mp eq1') with hb1 hb1
      · -- Case b = 0
        have hb0 : b = 0 := by linarith
        have hc0 : c = 0 := by 
          nlinarith [hc, ha1', hb0]
        left
        exact ⟨by linarith, by linarith, by linarith⟩
      · -- Case b = 1
        have hb1' : b = 1 := by linarith
        have hc1 : c = -1 := by
          nlinarith [hc, ha1', hb1']
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
    · -- If a ≠ 0
      have eq4 : a + 2 * b + 1 = 0 := by
        apply (mul_eq_zero.mp eq3).resolve_left
        exact ha1
      have eq4' : a = -2 * b - 1 := by linarith
      cases' (mul_eq_zero.mp eq2) with h5 h6
      · -- If b + a = 0
        have hb0 : b = -a := by linarith
        have h7 : b = -1 := by 
          rw [hb0] at eq4'
          nlinarith
        have h8 : a = 1 := by
          linarith [eq4', h7]
        have h9 : c = 0 := by
          nlinarith [hc, h8, h7]
        right
        right
        right
        exact ⟨by linarith, by linarith, by linarith⟩
      · -- If b - a - 1 = 0
        have hb1 : b = a + 1 := by linarith
        have h7 : b = 0 := by 
          rw [hb1] at eq4'
          nlinarith
        have h8 : a = -1 := by 
          linarith [hb1, h7]
        have h9 : c = 1 := by 
          nlinarith [hc, h8, h7]
        right
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
  · -- Show that the four solutions satisfy the three equations.
    rintro (h | h | h | h)
    · -- Case (0, 0, 0)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (0, 1, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (-1, 0, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (1, -1, 0)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num