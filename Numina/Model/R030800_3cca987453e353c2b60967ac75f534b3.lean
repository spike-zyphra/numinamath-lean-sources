import Mathlib

theorem probability_16042 : {x | x ∈ Finset.Icc 1 24 ∧ x ∣ Nat.factorial 4}.ncard / 24 = 1 / 3 := by
  have h1 : Nat.factorial 4 = 24 := by
    norm_num [Nat.factorial]
  have h2 : {x | x ∈ Finset.Icc 1 24 ∧ x ∣ Nat.factorial 4} = 
      {1, 2, 3, 4, 6, 8, 12, 24} := by
    ext x
    simp [Finset.mem_Icc, h1]
    constructor
    · -- Assume x is in the set {x | x ∈ [1,24] ∧ x divides 24}
      intro h
      rcases h with ⟨⟨hx1, hx2⟩, hx3⟩
      interval_cases x <;> norm_num at *
    · -- Assume x is in {1,2,3,4,6,8,12,24}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · -- 1 is in [1,24]
          norm_num
        · -- 1 divides 24
          norm_num
      · -- x = 2
        constructor
        · -- 2 is in [1,24]
          norm_num
        · -- 2 divides 24
          norm_num
      · -- x = 3
        constructor
        · -- 3 is in [1,24]
          norm_num
        · -- 3 divides 24
          norm_num
      · -- x = 4
        constructor
        · -- 4 is in [1,24]
          norm_num
        · -- 4 divides 24
          norm_num
      · -- x = 6
        constructor
        · -- 6 is in [1,24]
          norm_num
        · -- 6 divides 24
          norm_num
      · -- x = 8
        constructor
        · -- 8 is in [1,24]
          norm_num
        · -- 8 divides 24
          norm_num
      · -- x = 12
        constructor
        · -- 12 is in [1,24]
          norm_num
        · -- 12 divides 24
          norm_num
      · -- x = 24
        constructor
        · -- 24 is in [1,24]
          norm_num
        · -- 24 divides 24
          norm_num
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }