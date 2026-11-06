import Mathlib

theorem algebra_21495 :
    (↑({x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)}.ncard) : ℝ) / (6 * 6) = 1 / 12 := by
  have h : {x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)} = {(1, 3), (2, 2), (3, 1)} := by
    ext ⟨a, b⟩
    simp [Int.mem_range_iff]
    constructor
    · -- Assume ⟨a, b⟩ ∈ {x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)}
      rintro ⟨ha, hb, hab⟩
      have h1 : a ≥ 1 := by
        omega
      have h2 : a ≤ 6 := by
        omega
      have h3 : b ≥ 1 := by
        omega
      have h4 : b ≤ 6 := by
        omega
      interval_cases a <;> omega
    · -- Show that each of the elements in {(1,3), (2,2), (3,1)} is in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (1, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (2, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (3, 1)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  all_goals norm_num