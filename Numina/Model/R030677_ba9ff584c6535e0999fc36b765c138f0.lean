import Mathlib

theorem algebra_21218 :
    {r : ℤ | ∃ x y : ℝ, r = ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋} = {0, 1}:= by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, show that if r is in the set, then r in {0, 1}
    intro h
    rcases h with ⟨x, y, h_eq⟩
    have h1 : ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋ = 0 ∨ ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋ = 1 := by
      have h2 : ⌊x + y⌋ ≥ ⌊x⌋ + ⌊y⌋ := by
        have h3 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
        have h4 : (⌊y⌋ : ℝ) ≤ y := by exact Int.floor_le y
        have h5 : (⌊x⌋ + ⌊y⌋ : ℝ) ≤ x + y := by linarith
        have h13 : ⌊x + y⌋ ≥ ⌊x⌋ + ⌊y⌋ := by
          by_contra h
          push_neg at h
          have h15 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ - 1 := by
            omega
          have h16 : (⌊x + y⌋ : ℝ) ≤ (⌊x⌋ + ⌊y⌋ - 1 : ℝ) := by
            exact_mod_cast h15
          have h17 : (⌊x + y⌋ : ℝ) ≤ x + y := by
            exact Int.floor_le (x + y)
          nlinarith [Int.floor_le (x + y), Int.lt_floor_add_one (x + y), Int.floor_le x, Int.floor_le y, Int.lt_floor_add_one x, Int.lt_floor_add_one y]
        omega
      -- Show that floor(x + y) ≤ floor(x) + floor(y) + 1
      have h3 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
        have h10 : x + y < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by
          have h11 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
          have h12 : y < (⌊y⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one y
          linarith
        have h14 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
          by_contra h
          push_neg at h
          have h15 : ⌊x + y⌋ ≥ ⌊x⌋ + ⌊y⌋ + 2 := by
            omega
          have h16 : (⌊x + y⌋ : ℝ) ≥ (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by
            exact_mod_cast h15
          have h17 : (⌊x + y⌋ : ℝ) ≤ x + y := by
            exact Int.floor_le (x + y)
          nlinarith [Int.floor_le (x + y), Int.lt_floor_add_one (x + y), Int.floor_le x, Int.floor_le y, Int.lt_floor_add_one x, Int.lt_floor_add_one y]
        omega
      omega
    rw [h_eq] at *
    rcases h1 with (h1 | h1)
    · -- difference is 0 
      left
      omega
    · -- difference is 1
      right
      omega
  · -- Prove the reverse direction
    rintro (h | h)
    · -- r = 0 
      rw [h]
      use (0 : ℝ), (0 : ℝ)
      all_goals norm_num
    · -- r = 1 
      rw [h]
      use (0.5 : ℝ), (0.6 : ℝ)
      norm_num