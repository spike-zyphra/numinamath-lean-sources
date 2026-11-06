import Mathlib

theorem algebra_5334 :
    ∑ᶠ xy ∈ {n : ℤ | ∃ x y : ℤ, n = x * y ∧ 6 * x + 3 * x * y - 4 * y = 21}, xy = -6 := by
  have h1 : {n : ℤ | ∃ x y : ℤ, n = x * y ∧ 6 * x + 3 * x * y - 4 * y = 21} = 
    {-15, 9} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n ∈ left, proving n ∈ right
      rintro ⟨x, y, hn, h⟩
      -- Equation: 6x + 3xy - 4y = 21
      -- Equation: 6x + y(3x - 4) = 21
      have h3 : (3 * x - 4) * (y + 2) = 13 := by
        nlinarith
      have h5 : (3 * x - 4) * (y + 2) = 13 := h3
      have h8 : (3 * x - 4) ∣ 13 := by
        use (y + 2)
        all_goals linarith
      have h9 : (3 * x - 4) = 1 ∨ (3 * x - 4) = 13 ∨ (3 * x - 4) = -1 ∨ (3 * x - 4) = -13 := by 
        have h8' : (3 * x - 4) ∣ 13 := h8
        have h10 : (3 * x - 4) ≤ 13 := by
          exact Int.le_of_dvd (by norm_num) h8'
        have h11 : (3 * x - 4) ≥ -13 := by
          have h12 : (- (3 * x - 4)) ∣ 13 := by 
            exact Int.neg_dvd.2 h8'
          have h13 : - (3 * x - 4) ≤ 13 := by 
            exact Int.le_of_dvd (by norm_num) h12
          omega
        interval_cases (3 * x - 4) <;> tauto
      rcases h9 with (h10 | h10 | h10 | h10)
      · -- 3 * x - 4 = 1
        have h11 : (3 * x - 4) = 1 := h10
        have h12 : y + 2 = 13 := by
          rw [h11] at h5
          linarith
        -- 3 *x -4 =1 ⇒3x=5 ⇒x=5/3 not integer
        have h13 : 3 * x = 5 := by
          omega
        omega
      · -- 3 * x - 4 = 13
        have h14 : (3 * x - 4) = 13 := h10
        have h15 : y + 2 = 1 := by
          rw [h14] at h5
          linarith
        have h16 : 3 * x = 17 := by 
          omega
        omega
      · -- 3 * x - 4 = -1
        have h17 : (3 * x - 4) = -1 := h10
        have h18 : y + 2 = -13 := by
          rw [h17] at h5
          linarith
        have hx : x = 1 := by
          omega
        have hy : y = -15 := by
          omega
        rw [hn]
        rw [hx, hy]
        all_goals norm_num
      · -- 3 * x - 4 = -13
        have h17 : (3 * x - 4) = -13 := h10
        have h18 : y + 2 = -1 := by
          rw [h17] at h5
          linarith
        have hx : x = -3 := by
          omega
        have hy : y = -3 := by
          omega
        rw [hn]
        rw [hx, hy]
        all_goals norm_num 
    · -- Assume n ∈ right, proving n ∈ left
      rintro (rfl | rfl)
      · -- n = -15
        exact ⟨1, -15, by norm_num, by norm_num⟩
      · -- n = 9
        exact ⟨-3, -3, by norm_num, by norm_num⟩
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num