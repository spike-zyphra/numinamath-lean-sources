import Mathlib

theorem algebra_318749 :
    Set.ncard {n : ℤ | ∃ x y z : ℝ, n = ⌊x - y + z⌋ ∧ ⌊x⌋ = 5 ∧ ⌊y⌋ = -3 ∧ ⌊z⌋ = -2} = 3 := by
  have h1 : {n : ℤ | ∃ x y z : ℝ, n = ⌊x - y + z⌋ ∧ ⌊x⌋ = 5 ∧ ⌊y⌋ = -3 ∧ ⌊z⌋ = -2} = {5, 6, 7} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume there are x, y, z satisfying the conditions, prove n ∈ {5, 6, 7}
      rintro ⟨x, y, z, hn, hx1, hy1, hz1⟩
      have h2 : 5 ≤ x := by
        have h2 : ⌊x⌋ = 5 := hx1
        have h3 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
        have h4 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
        have h5 : (⌊x⌋ : ℝ) = (5 : ℝ) := by
          exact_mod_cast h2
        rw [h5] at h3
        have h6 : x < (6 : ℝ) := by
          have h7 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
          have h8 : (⌊x⌋ + 1 : ℝ) = (6 : ℝ) := by
            rw [h5]
            all_goals norm_num
          linarith
        nlinarith
      have h3 : x < (6 : ℝ) := by
        have h2 : ⌊x⌋ = 5 := hx1
        have h3 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
        have h4 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
        have h5 : (⌊x⌋ : ℝ) = (5 : ℝ) := by
          exact_mod_cast h2
        rw [h5] at h4
        norm_num at h4 ⊢
        linarith
      have h4 : (-3 : ℝ) ≤ y := by
        have h5 : ⌊y⌋ = -3 := hy1
        have h6 : (⌊y⌋ : ℝ) ≤ y := by exact Int.floor_le y
        have h7 : (⌊y⌋ : ℝ) = (-3 : ℝ) := by
          exact_mod_cast h5
        linarith
      have h5 : y < (-2 : ℝ) := by
        have h6 : ⌊y⌋ = -3 := hy1
        have h7 : y < (⌊y⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one y
        have h8 : (⌊y⌋ + 1 : ℝ) = (-2 : ℝ) := by
          rw [h6]
          all_goals norm_num
        linarith
      have h6 : (-2 : ℝ) ≤ z := by
        have h8 : ⌊z⌋ = -2 := hz1
        have h9 : (⌊z⌋ : ℝ) ≤ z := by exact Int.floor_le z
        have h10 : (⌊z⌋ : ℝ) = (-2 : ℝ) := by
          exact_mod_cast h8
        linarith
      have h7 : z < (-1 : ℝ) := by
        have h9 : ⌊z⌋ = -2 := hz1
        have h10 : z < (⌊z⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one z
        have h11 : (⌊z⌋ + 1 : ℝ) = (-1 : ℝ) := by
          rw [h9]
          all_goals norm_num
        linarith
      have h8 : (n : ℝ) ≤ x - y + z := by
        have h9 : n = ⌊x - y + z⌋ := hn
        have h10 : (⌊x - y + z⌋ : ℝ) ≤ x - y + z := by exact Int.floor_le (x - y + z)
        rw [show (⌊x - y + z⌋ : ℝ) = (n : ℝ) by exact_mod_cast (show ⌊x - y + z⌋ = n by linarith [hn] )] at h10
        linarith
      have h9 : x - y + z < (n + 1 : ℝ) := by
        have h11 : n = ⌊x - y + z⌋ := hn
        have h12 : x - y + z < (⌊x - y + z⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x - y + z)
        have h13 : (⌊x - y + z⌋ : ℝ) = (n : ℝ) := by
          exact_mod_cast (show ⌊x - y + z⌋ = n by linarith [hn] )
        rw [h13] at h12
        linarith
      have h11 : (5 : ℝ) ≤ x - y + z := by
        nlinarith
      have h12 : x - y + z < (8 : ℝ) := by
        nlinarith
      have h13 : n ≤ 7 := by
        by_contra h14
        push_neg at h14
        have h14' : n ≥ 8 := by omega
        have h15 : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast h14'
        nlinarith
      have h14 : n ≥ 5 := by
        by_contra h15
        push_neg at h15
        have h16 : n ≤ 4 := by omega
        have h17 : (n : ℝ) ≤ (4 : ℝ) := by exact_mod_cast h16
        nlinarith
      omega
    · -- Assume n = 5,6,7, prove existence of x, y, z
      rintro (rfl | rfl | rfl)
      · -- n = 5
        use (5 : ℝ), (-2.1 : ℝ), (-2 : ℝ)
        norm_num [Int.floor_eq_iff]
      · -- n = 6
        use (5.5 : ℝ), (-2.5 : ℝ), (-1.5 : ℝ)
        norm_num [Int.floor_eq_iff]
      · -- n = 7
        use (5.9 : ℝ), (-2.9 : ℝ), (-1.1 : ℝ)
        norm_num [Int.floor_eq_iff]
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]