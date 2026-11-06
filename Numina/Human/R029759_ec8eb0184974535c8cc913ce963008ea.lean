import Mathlib

/-A lattice point is a point in the plane with integer coordinates. How many lattice points are on the line segment whose endpoints are (3,17) and (48,281)?(Include both endpoints of the segment in your count.)-/
theorem number_theory_96473 : {(x, y) : ℤ × ℤ | x ≥ 3 ∧ y ≥ 17 ∧ x ≤ 48 ∧ y ≤ 281 ∧
    (x - 3) * (281 - 17) = (y - 17) * (48 - 3)}.ncard = 4 := by
    -- compute the set directly
  have : {(x, y) : ℤ × ℤ | x ≥ 3 ∧ y ≥ 17 ∧ x ≤ 48 ∧ y ≤ 281 ∧
    (x - 3) * (281 - 17) = (y - 17) * (48 - 3)} = {(3, 17), (18, 105), (33, 193), (48, 281)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, we need to prove that if (x, y) is in the set on the left, then it's in the set on the right
      rintro ⟨hx1, hy1, hx2, hy2, hline⟩
      have h1 : x ≤ 48 := hx2
      have h2 : y ≤ 281 := hy2
      have h3 : (x - 3) * 264 = (y - 17) * 45 := by linarith
      have h4 : x ≥ 3 := hx1
      have h5 : y ≥ 17 := hy1
      have h6 : (x - 3) = 0 ∨ (x - 3) = 15 ∨ (x - 3) = 30 ∨ (x - 3) = 45 := by
        omega
      rcases h6 with (h6 | h6 | h6 | h6)
      · -- x - 3 = 0
        have hx : x = 3 := by linarith
        have hy : y = 17 := by
          rw [hx] at h3
          omega
        exact Or.inl ⟨hx, hy⟩
      · -- x - 3 = 15
        have hx : x = 18 := by linarith
        have hy : y = 105 := by
          rw [hx] at h3
          omega
        exact Or.inr (Or.inl ⟨hx, hy⟩)
      · -- x - 3 = 30
        have hx : x = 33 := by linarith
        have hy : y = 193 := by
          rw [hx] at h3
          omega
        exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
      · -- x - 3 = 45
        have hx : x = 48 := by linarith
        have hy : y = 281 := by
          rw [hx] at h3
          omega
        exact Or.inr (Or.inr (Or.inr ⟨hx, hy⟩))
    · -- Now prove the reverse: if (x, y) is in the finite set, then it's in the original set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (3, 17)
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- (18, 105)
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- (33, 193)
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- (48, 281)
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]