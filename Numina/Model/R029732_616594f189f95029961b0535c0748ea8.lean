import Mathlib

open Real BigOperators Set

theorem inequalities_166640 :
    {(x, y) : ℤ × ℤ | ((y : ℝ) + (1 : ℝ) / 2 > abs ((x : ℝ) ^ 2 - 2 * (x : ℝ)) ∧ 
    (y : ℝ) ≤ 2 - abs ((x : ℝ) - 1))} =
    {(0, 0), (0, 1), (1, 1), (1, 2), (2, 0), (2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First direction: If (x,y) satisfies both inequalities, then (x,y) ∈ {(0,0), (0,1), (1,1), (1,2), (2,0), (2,1)}.
    rintro ⟨h₁, h₂⟩
    have h3 : x ≥ 0 := by
      by_contra h
      push_neg at h
      have h4 : x ≤ -1 := by omega
      have h4' : (x : ℝ) ≤ -1 := by exact_mod_cast h4
      have h5 : abs ((x : ℝ) ^ 2 - 2 * (x : ℝ)) ≥ (3 : ℝ) := by
        have h10 : (x : ℝ) ≤ -1 := h4'
        have h14 : (x : ℝ) ^ 2 - 2 * (x : ℝ) ≥ (3 : ℝ) := by
          nlinarith [sq_nonneg ((x : ℝ) + 1)]
        have h15 : abs ((x : ℝ) ^ 2 - 2 * (x : ℝ)) = (x : ℝ) ^ 2 - 2 * (x : ℝ) := by
          rw [abs_of_nonneg]
          nlinarith
        linarith
      have h14 : (y : ℝ) > (3 : ℝ) - (1 : ℝ) / 2 := by linarith [h5, h₁]
      have h43 : abs ((x : ℝ) - 1) ≥ (2 : ℝ) := by
        have h44 : (x : ℝ) ≤ -1 := h4'
        have h45 : (x : ℝ) - 1 ≤ -2 := by nlinarith
        have h101 : abs ((x : ℝ) - 1) = abs ((x : ℝ) - 1) := by rfl
        have h101 : abs ((x : ℝ) - 1) ≥ (2 : ℝ) := by
          rw [abs_of_nonpos (show (x : ℝ) - 1 ≤ 0 by nlinarith)]
          all_goals
          nlinarith [sq_nonneg ((x : ℝ) - 1)]
        linarith
      nlinarith [abs_nonneg ((x : ℝ) ^ 2 - 2 * (x : ℝ)), abs_nonneg ((x : ℝ) - 1), abs_nonneg ((x : ℝ) ^ 2 - 2 * (x : ℝ)), abs_nonneg ((x : ℝ) - 1)]
    -- Show that x ≤ 2.
    have h4 : x ≤ 2 := by
      by_contra h
      push_neg at h
      have h5 : x ≥ 3 := by omega
      have h5' : (x : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h5
      have h6 : abs ((x : ℝ) ^ 2 - 2 * (x : ℝ)) ≥ (3 : ℝ) := by
        have h13 : (x : ℝ) ≥ (3 : ℝ) := h5'
        have h14 : (x : ℝ)^2 - 2 * (x : ℝ) ≥ (3 : ℝ) := by
          nlinarith [sq_nonneg ((x : ℝ) - 1)]
        have h15 : abs ((x : ℝ) ^ 2 - 2 * (x : ℝ)) = (x : ℝ) ^ 2 - 2 * (x : ℝ) := by
          rw [abs_of_nonneg]
          nlinarith
        linarith
      have h7 : (y : ℝ) > (3 : ℝ) - (1 : ℝ) / 2 := by linarith [h₁, h6]
      have h43 : abs ((x : ℝ) - 1) ≥ (2 : ℝ) := by
        have h44 : (x : ℝ) ≥ (3 : ℝ) := h5'
        have h45 : (x : ℝ) - 1 ≥ (2 : ℝ) := by nlinarith
        have h101 : abs ((x : ℝ) - 1) = abs ((x : ℝ) - 1) := by rfl
        have h101 : abs ((x : ℝ) - 1) ≥ (2 : ℝ) := by
          rw [abs_of_nonneg (show (x : ℝ) - 1 ≥ 0 by nlinarith)]
          all_goals
          nlinarith
        linarith
      nlinarith [abs_nonneg ((x : ℝ) ^ 2 - 2 * (x : ℝ)), abs_nonneg ((x : ℝ) - 1), abs_nonneg ((x : ℝ) ^ 2 - 2 * (x : ℝ)), abs_nonneg ((x : ℝ) - 1)]
    -- So, x ∈ {0, 1, 2}.
    have hx : x = 0 ∨ x = 1 ∨ x = 2 := by
      omega
    rcases hx with (r | r | r)
    · -- x = 0.
      have hx0 : (x : ℝ) = (0 : ℝ) := by exact_mod_cast (show x = (0 : ℤ) by linarith)
      rw [hx0] at h₁ h₂
      have h3 : y ≤ 1 := by
        have h4 : (y : ℝ) ≤ (2 : ℝ) - abs ((0 : ℝ) - 1) := by linarith [h₂]
        norm_num [abs] at h4 ⊢
        exact_mod_cast h4
      have h4 : y ≥ 0 := by
        have h5 : (y : ℝ) + (1 / 2 : ℝ) > abs ((0 : ℝ) ^ 2 - 2 * (0 : ℝ)) := by linarith [h₁]
        norm_num [abs] at h5 ⊢
        have h6 : y ≥ 0 := by
          by_contra h
          push_neg at h
          have : y ≤ -1 := by omega
          have h7 : (y : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast this
          nlinarith
        linarith
      have h7 : y = 0 ∨ y = 1 := by
        omega
      rcases h7 with (h7 | h7)
      · -- y = 0
        left
        simp [r, h7]
      · -- y = 1
        right
        left
        simp [r, h7]
    · -- x = 1.
      have hx1 : (x : ℝ) = (1 : ℝ) := by exact_mod_cast (show x = (1 : ℤ) by linarith)
      rw [hx1] at h₁ h₂
      have h3 : y ≤ 2 := by
        have h4 : (y : ℝ) ≤ (2 : ℝ) - abs ((1 : ℝ) - 1) := by linarith [h₂]
        norm_num [abs] at h4 ⊢
        exact_mod_cast h4
      have h4 : y ≥ 1 := by
        have h5 : (y : ℝ) + (1 / 2 : ℝ) > abs ((1 : ℝ) ^ 2 - 2 * (1 : ℝ)) := by linarith [h₁]
        norm_num [abs] at h5 ⊢
        have h6 : y ≥ 1 := by
          by_contra h
          push_neg at h
          have : y ≤ 0 := by omega
          have h7 : (y : ℝ) ≤ (0 : ℝ) := by exact_mod_cast this
          nlinarith
        linarith
      have h7 : y = 1 ∨ y = 2 := by
        omega
      rcases h7 with (h7 | h7)
      · -- y = 1
        right
        right
        left
        simp [r, h7]
      · -- y = 2
        right
        right
        right
        left
        simp [r, h7]
    · -- x = 2.
      have hx2 : (x : ℝ) = (2 : ℝ) := by exact_mod_cast (show x = (2 : ℤ) by linarith)
      rw [hx2] at h₁ h₂
      have h3 : y ≤ 1 := by
        have h4 : (y : ℝ) ≤ (2 : ℝ) - abs ((2 : ℝ) - 1) := by linarith [h₂]
        norm_num [abs] at h4 ⊢
        exact_mod_cast h4
      have h4 : y ≥ 0 := by
        have h5 : (y : ℝ) + (1 / 2 : ℝ) > abs ((2 : ℝ) ^ 2 - 2 * (2 : ℝ)) := by linarith [h₁]
        norm_num [abs] at h5 ⊢
        have h6 : y ≥ 0 := by
          by_contra h
          push_neg at h
          have : y ≤ -1 := by omega
          have h7 : (y : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast this
          nlinarith
        linarith
      have h7 : y = 0 ∨ y = 1 := by
        omega
      rcases h7 with (h7 | h7)
      · -- y = 0
        right
        right
        right
        right
        left
        simp [r, h7]
      · -- y = 1
        right
        right
        right
        right
        right
        simp [r, h7]
  · -- Second direction: If (x,y) ∈ {(0,0), (0,1), (1,1), (1,2), (2,0), (2,1)}, then (x,y) satisfies both inequalities.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl
      ⟩ | ⟨rfl, rfl⟩)
    · -- (0, 0)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]
    · -- (0, 1)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]
    · -- (1, 1)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]
    · -- (1, 2)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]
    · -- (2, 0)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]
    · -- (2, 1)
      constructor
      · -- Check the first inequality
        norm_num [abs]
      · -- Check the second inequality
        norm_num [abs]