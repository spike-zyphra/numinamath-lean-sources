import Mathlib

theorem algebra_318269 :
    {p : ℤ | p ≠ 0 ∧ ∃! x : ℤ, p * x = x + 10}.encard = 7 := by
  have h1 : {p : ℤ | p ≠ 0 ∧ ∃! x : ℤ, p * x = x + 10} = {2, 3, -1, 6, -4, 11, -9} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume p in the set, prove p in the finite set
      intro h
      rcases h with ⟨hp_ne, ⟨x, ⟨hx1, hx2⟩⟩⟩
      have eq1 : p * x = x + 10 := hx1
      have h2 : x * (p - 1) = 10 := by
        nlinarith
      have h3 : (p - 1) ∣ 10 := by
        use x
        all_goals linarith
      have h4 : (p - 1) = 1 ∨ (p - 1) = -1 ∨ (p - 1) = 2 ∨ (p - 1) = -2 ∨ (p - 1) = 5 ∨ (p - 1) = -5 ∨ (p - 1) = 10 ∨ (p - 1) = -10 := by
        have h3' : (p - 1) ∣ 10 := h3
        have h5 : (p - 1) ≤ 10 := by
          apply Int.le_of_dvd (by norm_num) h3'
        have h6 : (p - 1) ≥ -10 := by
          have h5' : (p - 1) ∣ 10 := h3
          have h7 : (- (p - 1)) ∣ 10 := by
            exact Int.neg_dvd.2 h5'
          have h8 : - (p - 1) ≤ 10 := by
            apply Int.le_of_dvd (by norm_num) h7
          omega
        interval_cases (p - 1) <;> tauto
      rcases h4 with (h | h | h | h | h | h | h | h)
      · -- p - 1 = 1, so p = 2
        have hp1 : p = 2 := by linarith
        simp [hp1]
      · -- p - 1 = -1, so p = 0
        have hp0 : p = 0 := by linarith
        exfalso
        apply hp_ne
        linarith
      · -- p - 1 = 2, so p = 3
        have hp3 : p = 3 := by linarith
        simp [hp3]
      · -- p - 1 = -2, so p = -1
        have hpN1 : p = -1 := by linarith
        simp [hpN1]
      · -- p - 1 = 5, so p = 6
        have hp6 : p = 6 := by linarith
        simp [hp6]
      · -- p - 1 = -5, so p = -4
        have hpN4 : p = -4 := by linarith
        simp [hpN4]
      · -- p - 1 = 10, so p = 11
        have hp11 : p = 11 := by linarith
        simp [hp11]
      · -- p - 1 = -10, so p = -9
        have hpN9 : p = -9 := by linarith
        simp [hpN9]
    · -- Assume p in the finite set, prove p in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- p = 2
        constructor
        · -- 2 ≠ 0
          norm_num
        · -- ∃! x, 2 * x = x + 10
          use 10
          constructor
          · -- Show 2 * 10 = 10 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = 10
            intro y hy
            have eq2 : (2 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = 3
        constructor
        · -- 3 ≠ 0
          norm_num
        · -- ∃! x, 3 * x = x + 10
          use 5
          constructor
          · -- Show 3 * 5 = 5 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = 5
            intro y hy
            have eq2 : (3 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = -1
        constructor
        · -- -1 ≠ 0
          norm_num
        · -- ∃! x, -1 * x = x + 10
          use -5
          constructor
          · -- Show -1 * (-5) = -5 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = -5
            intro y hy
            have eq2 : (-1 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = 6
        constructor
        · -- 6 ≠ 0
          norm_num
        · -- ∃! x, 6 * x = x + 10
          use 2
          constructor
          · -- Show 6 * 2 = 2 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = 2
            intro y hy
            have eq2 : (6 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = -4
        constructor
        · -- -4 ≠ 0
          norm_num
        · -- ∃! x, -4 * x = x + 10
          use -2
          constructor
          · -- Show -4 * (-2) = -2 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = -2
            intro y hy
            have eq2 : (-4 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = 11
        constructor
        · -- 11 ≠ 0
          norm_num
        · -- ∃! x, 11 * x = x + 10
          use 1
          constructor
          · -- Show 11 * 1 = 1 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = 1
            intro y hy
            have eq2 : (11 : ℤ) * y = y + 10 := hy
            linarith
      · -- p = -9
        constructor
        · -- -9 ≠ 0
          norm_num
        · -- ∃! x, -9 * x = x + 10
          use -1
          constructor
          · -- Show -9 * (-1) = -1 + 10
            norm_num
          · -- Show uniqueness: if y satisfies the equation, y = -1
            intro y hy
            have eq2 : (-9 : ℤ) * y = y + 10 := hy
            linarith
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }