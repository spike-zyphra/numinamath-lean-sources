import Mathlib

theorem algebra_102387 : {(x, y) : ℤ × ℤ | x * y - 3 * x + 5 * y = 0}.ncard = 8 := by
  have h2 : {(x, y) : ℤ × ℤ | x * y - 3 * x + 5 * y = 0} = { 
    (-20, 4), (-10, 6), (-8, 8), (-6, 18), 
    (-4, -12), (-2, -2), (0, 0), (10, 2)
  } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume that (x, y) satisfies the equation, prove (x, y) ∈ RHS
      rintro H
      have : (x + 5) * (y - 3) = -15 := by
        nlinarith
      have h3 : (x + 5) ∣ (-15 : ℤ) := by 
        use y - 3
        all_goals linarith
      have h4 : (x + 5) ∣ (15 : ℤ) := by 
        exact Int.dvd_neg.mp h3
      have h5 : (x + 5) = -15 ∨ (x + 5) = -5 ∨ (x + 5) = -3 ∨ (x + 5) = -1 ∨ (x + 5) = 1 ∨ (x + 5) = 3 ∨ (x + 5) = 5 ∨ (x + 5) = 15 := by
        have h6 : (x + 5) ∣ (15 : ℤ) := h4
        have h7 : (x + 5) ≤ 15 := by
          apply Int.le_of_dvd (by norm_num) h6
        have h8 : (x + 5) ≥ -15 := by
          have h9 : (- (x + 5)) ∣ (15 : ℤ) := by
            exact Int.neg_dvd.2 h6
          have h10 : - (x + 5) ≤ 15 := by
            apply Int.le_of_dvd (by norm_num) h9
          omega
        interval_cases h : (x + 5) <;> tauto
      rcases h5 with (h | h | h | h | h | h | h | h)
      · -- Case x +5 = -15. Then y - 3 = 1, so y = 4
        have hx : x = -20 := by linarith
        have hy : y = 4 := by
          rw [show x + 5 = -15 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = -5. Then y - 3 = 3, so y = 6
        have hx : x = -10 := by linarith
        have hy : y = 6 := by
          rw [show x + 5 = -5 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = -3. Then y - 3 = 5, so y = 8
        have hx : x = -8 := by linarith
        have hy : y = 8 := by
          rw [show x + 5 = -3 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = -1. Then y - 3 = 15, so y = 18
        have hx : x = -6 := by linarith
        have hy : y = 18 := by
          rw [show x + 5 = -1 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = 1. Then y - 3 = -15, so y = -12
        have hx : x = -4 := by linarith
        have hy : y = -12 := by
          rw [show x + 5 = 1 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = 3. Then y - 3 = -5, so y = -2
        have hx : x = -2 := by linarith
        have hy : y = -2 := by
          rw [show x + 5 = 3 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = 5. Then y - 3 = -3, so y = 0
        have hx : x = 0 := by linarith
        have hy : y = 0 := by
          rw [show x + 5 = 5 by linarith [h]] at this
          linarith
        simp [hx, hy]
      · -- Case x +5 = 15. Then y - 3 = -1, so y = 2
        have hx : x = 10 := by linarith
        have hy : y = 2 := by
          rw [show x + 5 = 15 by linarith [h]] at this
          linarith
        simp [hx, hy]
    · -- Assume that (x, y) ∈ RHS, prove (x, y) satisfies the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { native_decide }