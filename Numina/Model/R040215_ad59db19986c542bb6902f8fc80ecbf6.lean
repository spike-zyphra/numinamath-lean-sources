import Mathlib

theorem algebra_94650 :
    Set.ncard {x : ℝ | ⌊x⌋^2 - 3 * x + 2 = 0} = 4 := by
  have h1 : {x : ℝ | ⌊x⌋^2 - 3 * x + 2 = 0} = {2 / 3, (1 : ℝ), (2 : ℝ), (11 / 3)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume that x satisfies the equation.
      intro h_eq
      have h2 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
      have h3 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
      have h4 : (⌊x⌋ : ℝ) ^ 2 - 3 * x + 2 = (0 : ℝ) := by simpa using h_eq
      have hx_eq : x = ((⌊x⌋ : ℝ) ^2 + 2) / 3 := by
        linarith
      have h5 : ⌊x⌋ ≤ 3 := by
        by_contra h
        push_neg at h
        have h6 : ⌊x⌋ ≥ 4 := by omega
        have h7 : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h6
        have h8 : x = ((⌊x⌋ : ℝ) ^2 + 2) / 3 := hx_eq
        have h9 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
        nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
      have h9 : ⌊x⌋ ≥ 0 := by
        by_contra h
        push_neg at h
        have h10 : ⌊x⌋ ≤ -1 := by omega
        have h11 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h10
        have h12 : x = ((⌊x⌋ : ℝ) ^ 2 + 2) / 3 := hx_eq
        have h13 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
        have h14 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
        nlinarith [Int.floor_le x, Int.lt_floor_add_one x, sq_nonneg ((⌊x⌋ : ℝ) + (1 : ℝ)), sq_nonneg (x - 1)]
      have h10 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 := by
        omega
      rcases h10 with (h11 | h11 | h11 | h11)
      · -- Case 0
        have h12 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h11
        rw [h12] at hx_eq
        norm_num at hx_eq
        rw [hx_eq]
        norm_num
      · -- Case 1
        have h12 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h11
        rw [h12] at hx_eq
        norm_num at hx_eq
        rw [hx_eq]
        norm_num
      · -- Case 2
        have h12 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h11
        rw [h12] at hx_eq
        norm_num at hx_eq
        rw [hx_eq]
        norm_num
      · -- Case 3
        have h12 : (⌊x⌋ : ℝ) = (3 : ℝ) := by exact_mod_cast h11
        rw [h12] at hx_eq
        norm_num at hx_eq
        rw [hx_eq]
        norm_num
    · -- Show that these four values satisfy the equation.
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 2/3
        norm_num
      · -- x = 1
        norm_num
      · -- x = 2
        norm_num
      · -- x = 11/3
        norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]