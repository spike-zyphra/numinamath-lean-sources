import Mathlib


theorem number_theory_162499 : {(x, y) : ℤ × ℤ | (2 * x + y) ^ 2 = 2017 + x ^ 2}.encard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | (2 * x + y) ^ 2 = 2017 + x ^ 2} = {(-1008, 1007), (-1008, 3025), (1008, -1007), (1008, -3025)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) satisfies (2x+y)^2 = 2017 + x^2, prove (x,y) ∈ {(1008, -1007), (1008, -3025), (-1008, 3025), (-1008, 1007)}
      rintro H
      have h_eq3 : (x + y) * (3 * x + y) = 2017 := by
        nlinarith
      have h3 : (x + y) ∣ 2017 := by
        use (3 * x + y)
        all_goals linarith
      have h4 : (x + y) = 1 ∨ (x + y) = -1 ∨ (x + y) = 2017 ∨ (x + y) = -2017 := by
        have h5 : (x + y) ∣ 2017 := h3
        have h6 : (x + y) ≤ 2017 := by
          apply Int.le_of_dvd (by norm_num) h5
        have h7 : (x + y) ≥ -2017 := by
          have h8 : -(x + y) ∣ 2017 := by
            exact Int.neg_dvd.2 h5
          have h9 : -(x + y) ≤ 2017 := by
            apply Int.le_of_dvd (by norm_num) h8
          linarith
        interval_cases h : (x + y) <;> tauto
      rcases h4 with h4 | h4 | h4 | h4
      · -- Case x+y = 1
        have h5 : (3 * x + y) = 2017 := by
          rw [show (x + y) = 1 by linarith [h4]] at h_eq3
          linarith
        have hx1 : x = 1008 := by
          linarith
        have hy1 : y = -1007 := by
          linarith [hx1, h4]
        simp [hx1, hy1]
      · -- Case x+y = -1
        have h5 : (3 * x + y) = -2017 := by
          rw [show (x + y) = -1 by linarith [h4]] at h_eq3
          linarith
        have hx1 : x = -1008 := by
          linarith
        have hy1 : y = 1007 := by
          linarith [hx1, h4]
        simp [hx1, hy1]
      · -- Case x+y = 2017
        have h5 : (3 * x + y) = 1 := by
          rw [show (x + y) = 2017 by linarith [h4]] at h_eq3
          linarith
        have hx1 : x = -1008 := by
          linarith
        have hy1 : y = 3025 := by
          linarith [hx1, h4]
        simp [hx1, hy1]
      · -- Case x+y = -2017
        have h5 : (3 * x + y) = -1 := by
          rw [show (x + y) = -2017 by linarith [h4]] at h_eq3
          linarith
        have hx1 : x = 1008 := by
          linarith
        have hy1 : y = -3025 := by
          linarith [hx1, h4]
        simp [hx1, hy1]
    · -- Assume (x,y) ∈ {(1008, -1007), (1008, -3025), (-1008, 3025), (-1008, 1007)}, prove (2x+y)^2 = 2017 + x^2
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (-1008, 1007)
        norm_num
      · -- Check (-1008, 3025)
        norm_num
      · -- Check (1008, -1007)
        norm_num
      · -- Check (1008, -3025)
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]