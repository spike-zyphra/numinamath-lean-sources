import Mathlib

theorem algebra_106611 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + x * z = 255 ∧ x * y + y * z = 31}.ncard = 2 := by
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + x * z = 255 ∧ x * y + y * z = 31} = { (15, 1, 16), (17, 1, 14) } := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- Forward direction: if (x, y, z) is in the set, it's one of the two pairs
      rintro ⟨hx, hy, hz, h1, h2⟩
      have h3 : y ∣ 31 := by
        use x + z
        nlinarith
      have h4 : y = 1 ∨ y = 31 := by 
        have h5 : y ≤ 31 := by
          exact Nat.le_of_dvd (by norm_num) h3
        interval_cases y <;> omega
      rcases h4 with hy1 | hy31
      · -- Case y = 1
        have h5 : x + z = 31 := by 
          rw [hy1] at h2
          nlinarith
        rw [hy1] at h1
        have h6 : z = 31 - x := by 
          omega
        rw [h6] at h1
        have h7 : x ≤ 32 := by 
          nlinarith
        interval_cases x <;> omega
      · -- Case y = 31
        have h5 : x + z = 1 := by 
          rw [hy31] at h2
          nlinarith
        have h6 : x + z ≥ 2 := by 
          omega
        linarith
    · -- Backward direction: show both given triples satisfy the system
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
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { aesop }
  <;> try { native_decide }