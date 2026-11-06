import Mathlib

theorem number_theory_96473 : {(x, y) : ℤ × ℤ | x ≥ 3 ∧ y ≥ 17 ∧ x ≤ 48 ∧ y ≤ 281 ∧
    (x - 3) * (281 - 17) = (y - 17) * (48 - 3)}.ncard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | x ≥ 3 ∧ y ≥ 17 ∧ x ≤ 48 ∧ y ≤ 281 ∧
      (x - 3) * (281 - 17) = (y - 17) * (48 - 3)} = {(3, 17), (18, 105), (33, 193), (48, 281)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) in the set
      rintro ⟨h1, h2, h3, h4, h5⟩
      have h : (x - 3) * 264 = (y - 17) * 45 := by
        nlinarith
      have h6 : (x - 3) % 15 = 0 := by
        omega
      have h7 : ∃ k : ℤ, x - 3 = 15 * k := by
        refine' ⟨(x - 3) / 15, by omega⟩
      rcases h7 with ⟨k, hk⟩
      have h8 : y - 17 = 88 * k := by
        rw [show x - 3 = 15 * k by linarith] at h
        omega
      have h9 : k ≥ 0 := by
        omega
      have h10 : k ≤ 3 := by
        omega
      have h11 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by 
        omega
      rcases h11 with (h12 | h13 | h14 | h15)
      · -- k = 0
        rw [show k = 0 by linarith] at h8 hk
        have hx0 : x = 3 := by 
          linarith 
        have hy0 : y = 17 := by 
          linarith 
        simp [hx0, hy0]
      · -- k = 1
        rw [show k = 1 by linarith] at h8 hk
        have hx1 : x = 18 := by 
          linarith 
        have hy1 : y = 105 := by 
          linarith 
        simp [hx1, hy1]
      · -- k = 2
        rw [show k = 2 by linarith] at h8 hk
        have hx2 : x = 33 := by 
          linarith 
        have hy2 : y = 193 := by 
          linarith 
        simp [hx2, hy2]
      · -- k = 3
        rw [show k = 3 by linarith] at h8 hk
        have hx3 : x = 48 := by 
          linarith 
        have hy3 : y = 281 := by 
          linarith 
        simp [hx3, hy3]
    · -- Show that (3, 17), (18, 105), (33, 193), (48, 281) are in the set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (3, 17)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (18, 105)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (33, 193)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (48, 281)
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
  <;> try { native_decide }