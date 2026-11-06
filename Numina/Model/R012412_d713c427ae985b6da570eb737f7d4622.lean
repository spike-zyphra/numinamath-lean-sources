import Mathlib

theorem algebra_223089 (x y : ℤ) :
    (x * y - 1) ^ 2 = (x + 1) ^ 2 + (y + 1) ^ 2 ↔
    (x, y) = (2, 3) ∨ (x, y) = (3, 2) ∨ (x, y) = (-1, y) ∨ (x, y) = (x, -1) := by
  constructor
  · -- Forward: if the equation holds, prove (x,y) = (2,3) ∨ (3,2) ∨ (-1,y) ∨ (x,-1)
    rintro h
    have h₁ : (x * y - 1) ^ 2 = (x + 1) ^ 2 + (y + 1) ^ 2 := h
    have h2 : (x * y - (x + y + 1)) * (x * y + (x + y + 1)) = 0 := by
      nlinarith [h₁]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case where $x * y - (x + y + 1) = 0$
      have h_eq : x * y = x + y + 1 := by linarith
      have h5 : (x - 1) * (y - 1) = 2 := by
        linarith [h_eq]
      have h6 : (x - 1) * (y - 1) = 2 := h5
      have h7 : (x - 1) ∣ 2 := by
        use (y - 1)
        all_goals linarith [h6]
      have h8 : (x - 1) = 1 ∨ (x - 1) = 2 ∨ (x - 1) = -1 ∨ (x - 1) = -2 := by
        have h7' : (x - 1) ∣ 2 := h7
        have h9 : (x - 1) ≤ 2 := by
          apply Int.le_of_dvd (by norm_num) h7'
        have h10 : (x - 1) ≥ -2 := by
          have h11 : (- (x - 1)) ∣ 2 := by
            exact Int.neg_dvd.2 h7'
          have h12 : - (x - 1) ≤ 2 := by
            apply Int.le_of_dvd (by norm_num) h11
          omega
        interval_cases (x - 1) <;> tauto
      rcases h8 with (h9 | h10 | h11 | h12)
      · -- x -1=1
        have hx : x = 2 := by linarith
        have hy : y = 3 := by nlinarith
        left
        simp [hx, hy]
      · -- x -1=2
        have hx : x = 3 := by linarith
        have hy : y = 2 := by nlinarith
        right
        left
        simp [hx, hy]
      · -- x -1=-1
        have hx : x = 0 := by linarith
        have hy : y = -1 := by nlinarith
        simp [hx, hy]
      · -- x -1=-2
        have hx : x = -1 := by linarith
        have hy : y = 0 := by nlinarith
        simp [hx, hy]
    · -- Case where $x * y + (x + y + 1) = 0$
      have h_eq : (x + 1) * (y + 1) = 0 := by
        linarith [h4]
      cases' (mul_eq_zero.1 h_eq) with h9 h10
      · -- x +1=0
        have hx : x = -1 := by linarith
        simp [hx]
      · -- y +1=0
        have hy : y = -1 := by linarith
        simp [hy]
  · -- Backward: prove the four possibilities satisfy the equation
    rintro (h | h | h | h)
    · -- (2, 3)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (3, 2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (-1, y)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals
        nlinarith
    · -- (x, -1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals
        nlinarith