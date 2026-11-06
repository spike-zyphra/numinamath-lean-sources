import Mathlib

theorem algebra_13066 : (∑ᶠ x ∈ {x : ℝ | 2 * x + 3 * Int.fract x = 4 * Int.floor x}, x) = 0 + 1.4 + 2.8 := by
  have h1 : {x : ℝ | 2 * x + 3 * Int.fract x = 4 * Int.floor x} = {0, 1.4, 2.8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: 2 * x + 3 * Int.fract x = 4 * Int.floor x
      intro h
      have h2 : Int.floor x ≤ x := by apply Int.floor_le
      have h3 : x < Int.floor x + 1 := by apply Int.lt_floor_add_one
      have h4 : Int.fract x = x - Int.floor x := by
        rw [Int.fract]
        <;> simp [Int.floor_le x, Int.lt_floor_add_one x]
        <;> linarith
      rw [h4] at h
      have h5 : (Int.floor x : ℝ) ≤ x := by exact_mod_cast h2
      have h6 : x < (Int.floor x + 1 : ℝ) := by exact_mod_cast h3
      have h7 : Int.floor x = (0 : Int) ∨ Int.floor x = (1 : Int) ∨ Int.floor x = (2 : Int) := by
        have h8 : Int.floor x ≤ 2 := by
          by_contra h9
          push_neg at h9
          have h9 : Int.floor x ≥ (3 : Int) := by omega
          have h9' : (Int.floor x : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h9
          nlinarith [h, h5, h6, Int.floor_le x, Int.lt_floor_add_one x]
        have h9 : Int.floor x ≥ (0 : Int) := by
          by_contra h9
          push_neg at h9
          have h9 : Int.floor x < (0 : Int) := by omega
          have h9' : (Int.floor x : ℝ) < (0 : ℝ) := by exact_mod_cast h9
          nlinarith [h, h5, h6, Int.floor_le x, Int.lt_floor_add_one x]
        interval_cases h10 : Int.floor x <;> try { tauto }
      rcases h7 with (h7 | h7 | h7)
      · -- Case Int.floor x = 0
        have h8 : (Int.floor x : ℝ) = (0 : ℝ) := by exact_mod_cast h7
        have hx : x = (0 : ℝ) := by nlinarith
        norm_num [hx]
      · -- Case Int.floor x = 1
        have h8 : (Int.floor x : ℝ) = (1 : ℝ) := by exact_mod_cast h7
        have hx : x = (7 / 5 : ℝ) := by nlinarith
        norm_num [hx]
        <;> linarith
      · -- Case Int.floor x = 2
        have h8 : (Int.floor x : ℝ) = (2 : ℝ) := by exact_mod_cast h7
        have hx : x = (14 / 5 : ℝ) := by nlinarith
        norm_num [hx]
        <;> linarith
    · -- Show that 0, 1.4, 2.8 are solutions
      rintro (rfl | rfl | rfl)
      · -- Check 0
        norm_num [Int.floor_eq_iff, Int.fract]
        <;> linarith
      · -- Check 1.4
        norm_num [Int.floor_eq_iff, Int.fract]
        <;> linarith
      · -- Check 2.8
        norm_num [Int.floor_eq_iff, Int.fract]
        <;> linarith
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num
  <;> ring_nf
  <;> norm_num