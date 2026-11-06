import Mathlib

theorem algebra_205810 : {(x, y) : ℤ × ℤ | x * y + 5 * x + 7 * y = 29}.encard = 14 := by
  have h1 : {(x, y) : ℤ × ℤ | x * y + 5 * x + 7 * y = 29} = {(-6,59), (-5,27), (-3,11), (1,3), (9,-1), (25,-3), (57,-4), 
   (-8,-69), (-9,-37), (-11,-21), (-15, -13), (-23,-9), (-39,-7), (-71,-6)
  } := by 
    ext ⟨x, y⟩
    simp 
    constructor 
    · -- Forward: if (x, y) is a solution, then it belongs to the right-hand side.
      rintro H
      have h1 : (x + 7) * (y + 5) = 64 := by
        nlinarith 
      have h2 : (x + 7) ∣ 64 := by 
        use y + 5
        all_goals nlinarith 
      have h3 : (x + 7) ≤ 64 := by 
        apply Int.le_of_dvd (show 0 < (64 : ℤ) by norm_num) h2 
      have h4 : (x + 7) ≥ -64 := by 
        have h5 : -(x + 7) ∣ 64 := by 
          exact Int.neg_dvd.2 h2 
        have h6 : -(x + 7) ≤ 64 := by 
          apply Int.le_of_dvd (show 0 < (64 : ℤ) by norm_num) h5 
        linarith 
      have h5 : (x + 7) = 1 ∨ (x + 7) = 2 ∨ (x + 7) = 4 ∨ (x + 7) = 8 ∨ (x + 7) = 16 ∨ (x + 7) = 32 ∨ (x + 7) = 64 ∨
      (x + 7) = -1 ∨ (x + 7) = -2 ∨ (x + 7) = -4 ∨ (x + 7) = -8 ∨ (x + 7) = -16 ∨ (x + 7) = -32 ∨ (x + 7) = -64 := by 
        interval_cases h : (x + 7) <;> tauto 
      rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5
      · -- Case 1: x + 7 = 1
        have h8 : (y + 5) = 64 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -6 := by 
          omega 
        have hy1 : y = 59 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- Case 2: x + 7 = 2
        have h8 : (y + 5) = 32 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -5 := by 
          omega 
        have hy1 : y = 27 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- Case 3: x + 7 = 4
        have h8 : (y + 5) = 16 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -3 := by 
          omega 
        have hy1 : y = 11 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- Case 4: x + 7 = 8
        have h8 : (y + 5) = 8 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = 1 := by 
          omega 
        have hy1 : y = 3 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- Case 5: x + 7 = 16
        have h8 : (y + 5) = 4 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = 9 := by 
          omega 
        have hy1 : y = -1 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 6 : x+7=32
        have h8 : (y + 5) = 2 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = 25 := by 
          omega 
        have hy1 : y = -3 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 7 : x+7=64
        have h8 : (y + 5) = 1 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = 57 := by 
          omega 
        have hy1 : y = -4 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 8 : x+7=-1
        have h8 : (y + 5) = -64 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -8 := by 
          omega 
        have hy1 : y = -69 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 9 : x+7=-2
        have h8 : (y + 5) = -32 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -9 := by 
          omega 
        have hy1 : y = -37 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 10 : x+7=-4
        have h8 : (y + 5) = -16 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -11 := by 
          omega 
        have hy1 : y = -21 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 11 : x+7=-8
        have h8 : (y + 5) = -8 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -15 := by 
          omega 
        have hy1 : y = -13 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 12 : x+7=-16
        have h8 : (y + 5) = -4 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -23 := by 
          omega 
        have hy1 : y = -9 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 13 : x+7=-32
        have h8 : (y + 5) = -2 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -39 := by 
          omega 
        have hy1 : y = -7 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
      · -- 14 : x+7=-64
        have h8 : (y + 5) = -1 := by 
          rw [h5] at h1
          nlinarith 
        have hx1 : x = -71 := by 
          omega 
        have hy1 : y = -6 := by 
          omega 
        simp [hx1, hy1] 
        <;> tauto 
    · -- Backward: if (x, y) is in the right-hand side set, it's a solution.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide