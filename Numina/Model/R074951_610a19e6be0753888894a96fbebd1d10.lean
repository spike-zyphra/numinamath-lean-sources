import Mathlib

theorem algebra_321019 :
    {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23}.ncard = 2 := by
  have h1 : {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23} = {(2, 21, 1), (20, 3, 1)} := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- Forward direction: if (x, y, z) satisfies the conditions, then it's one of the two found solutions
      rintro ⟨hx, hy, hz, h1, h2⟩
      have h3 : z ∣ 23 := by
        use x + y
        linarith
      have h4 : z = 1 ∨ z = 23 := by
        have h6 : z ∣ 23 := h3
        have h7 : z > 0 := hz
        have h8 : z ≤ 23 := by
          exact Int.le_of_dvd (by positivity) h6
        interval_cases z <;> tauto
      rcases h4 with (hz1 | hz23)
      · -- When z = 1, we derive the two solutions
        have h8 : x + y = 23 := by
          rw [hz1] at h2
          nlinarith
        have h9 : y * (x + 1) = 63 := by
          rw [hz1] at h1
          nlinarith
        have h10 : y = 21 ∨ y = 3 := by
          have eq1 : x + y = 23 := h8
          have h11 : x = 23 - y := by linarith
          rw [h11] at h9
          have h12 : (y - 21) * (y - 3) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h12) with h13 h14
          · -- Case where y - 21 = 0, so y = 21
            left
            linarith
          · -- Case where y -3 = 0, so y = 3
            right
            linarith
        rcases h10 with (hy21 | hy3)
        · -- When y = 21
          have h14 : x = 2 := by
            linarith
          have : x = 2 ∧ y = 21 ∧ z = 1 := ⟨h14, hy21, hz1⟩
          tauto
        · -- When y = 3
          have h16 : x = 20 := by
            linarith
          have : x = 20 ∧ y = 3 ∧ z = 1 := ⟨h16, hy3, hz1⟩
          tauto
      · -- Case z = 23, which leads to a contradiction
        have h24 : x + y = 1 := by
          rw [hz23] at h2
          nlinarith
        have : x + y ≥ 2 := by
          linarith
        linarith
    · -- Backward direction: if (x, y, z) is one of the two solutions, it satisfies the conditions
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- First solution
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Second solution
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num