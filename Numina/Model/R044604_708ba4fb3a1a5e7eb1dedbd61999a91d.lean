import Mathlib

theorem algebra_189287 (g : ℤ) (r : ℝ) :
    r / (r ^ 2 - 6 * r + 10) = g ↔
    (g, r) = (0, 0) ∨ (g, r) = (1, 5) ∨ (g, r) = (1, 2) ∨ (g, r) = (2, 4) ∨
    (g, r) = (2, 5 / 2) ∨ (g, r) = (3, 10 / 3) ∨ (g, r) = (3, 3) := by
  constructor
  · -- Assume r / (r ^ 2 - 6 * r + 10) = g, prove the disjunction of the solutions
    intro h
    have h1 : r ^ 2 - 6 * r + 10 > 0 := by 
      nlinarith [sq_nonneg (r - 3)]
    have eq1 : r = g * (r ^ 2 - 6 * r + 10) := by
      field_simp [show r ^ 2 - 6 * r + 10 ≠ 0 by linarith] at h ⊢
      linarith
    have eq2 : (g : ℝ) * r ^ 2 - (6 * (g : ℝ) + 1) * r + 10 * (g : ℝ) = 0 := by 
      nlinarith [eq1]
    have h2 : g ≤ 3 := by
      by_contra h3
      push_neg at h3
      have h3' : g ≥ 4 := by omega
      have h4 : (g : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h3'
      nlinarith [sq_nonneg ((g : ℝ) * r - (6 * (g : ℝ) + 1) / 2), sq_nonneg (r - 3), sq_nonneg ((g : ℝ) - 3), sq_nonneg ((g : ℝ)), sq_nonneg (r - 5 / 2)]
    have h3 : g ≥ 0 := by
      by_contra h4
      push_neg at h4
      have h4' : g ≤ -1 := by omega
      have h5 : (g : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h4'
      nlinarith [sq_nonneg ((g : ℝ) * r - (6 * (g : ℝ) + 1) / 2), sq_nonneg (r - 3), sq_nonneg ((g : ℝ) + 1), sq_nonneg (r - 5 / 2)]
    have h6 : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
    rcases h6 with (h6 | h6 | h6 | h6)
    · -- g = 0 
      have h7 : (g : ℝ) = (0 : ℝ) := by exact_mod_cast h6 
      rw [h7] at eq2 
      have h8 : r = 0 := by
        nlinarith 
      left 
      simp [h6, h8]
    · -- g = 1 
      have h7 : (g : ℝ) = (1 : ℝ) := by exact_mod_cast h6 
      rw [h7] at eq2 
      have h8 : r ^ 2 - 7 * r + 10 = 0 := by 
        nlinarith 
      have h9 : (r - 5) * (r - 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h10 h11 
      · -- r = 5 
        have h12 : r = 5 := by 
          linarith 
        right 
        left 
        simp [h6, h12]
      · -- r = 2 
        have h13 : r = 2 := by 
          linarith 
        right 
        right 
        left 
        simp [h6, h13]
    · -- g = 2 
      have h7 : (g : ℝ) = (2 : ℝ) := by exact_mod_cast h6 
      rw [h7] at eq2 
      have h8 : 2 * r ^ 2 - 13 * r + 20 = 0 := by 
        nlinarith 
      have h9 : (r - 4) * (2 * r - 5) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h11 h12 
      · -- r = 4 
        have h13 : r = 4 := by 
          linarith 
        right 
        right 
        right 
        left 
        simp [h6, h13]
      · -- 2 * r - 5 = 0 
        have h14 : r = 5 / 2 := by 
          linarith 
        right 
        right 
        right 
        simp [h6, h14]
    · -- g = 3 
      have h7 : (g : ℝ) = (3 : ℝ) := by exact_mod_cast h6 
      rw [h7] at eq2 
      have h8 : 3 * r ^ 2 - 19 * r + 30 = 0 := by 
        nlinarith 
      have h9 : (3 * r - 10) * (r - 3) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h11 h12 
      · -- 3 * r - 10 = 0 
        have h13 : r = 10 / 3 := by 
          linarith 
        right 
        right 
        right 
        right 
        right 
        simp [h6, h13]
      · -- r - 3 = 0 
        have h14 : r = 3 := by 
          linarith 
        right 
        right 
        right 
        right 
        right 
        right 
        simp [h6, h14]
  · -- Now prove the reverse direction 
    rintro (h | h | h | h | h | h | h)
    · -- (0, 0)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, 5)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, 2)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (2, 4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (2, 5/2)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (3, 10/3)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (3, 3)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num