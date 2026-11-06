import Mathlib

theorem algebra_325550 :
    {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23}.ncard = 2 := by
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23} = {(2, 21, 1), (20, 3, 1)} := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- First, prove the forward direction: if (x, y, z) is in the set, then (x, y, z) must be either (2, 21, 1) or (20, 3, 1)
      rintro ⟨hx, hy, hz, h1, h2⟩
      have h3 : z ∣ 23 := by
        use x + y
        linarith
      have h4 : z = 1 ∨ z = 23 := by
        have h5 : z ∣ 23 := h3
        have h6 : z ≤ 23 := by
          exact Nat.le_of_dvd (show 0 < 23 by norm_num) h5
        interval_cases z <;> norm_num at *
        all_goals try { tauto }
      rcases h4 with (hz1 | hz23)
      · -- Case where z = 1
        have h5 : x + y = 23 := by
          nlinarith
        have h6 : y * (x + 1) = 63 := by
          have : x * y + y * z = 63 := h1
          rw [hz1] at this
          nlinarith
        have h7 : y ≤ 23 := by linarith [h5]
        interval_cases y <;> omega
      · -- Case where z = 23
        have h8 : x + y = 1 := by
          nlinarith
        have h9 : x + y ≥ 2 := by
          linarith
        omega
    · -- Now prove the reverse direction: if (x, y, z) is either (2, 21, 1) or (20, 3, 1), then it's in the set
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]
  all_goals norm_num