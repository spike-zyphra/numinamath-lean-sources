import Mathlib

theorem algebra_608727 :
    ∑ᶠ x ∈ {x : ℝ | 0 < x ∧ 2 * x ^ 2 - ⌊x⌋ * x = 5}, x = (3 + Real.sqrt 41 + 2 * Real.sqrt 11) / 4 := by
  have h1 : {x : ℝ | 0 < x ∧ 2 * x ^ 2 - ⌊x⌋ * x = 5} = {(1 + Real.sqrt 41) / 4, (1 + Real.sqrt 11) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is a positive solution
      intro h
      rcases h with ⟨hx_pos, heq⟩
      let n := ⌊x⌋
      have h2 : n ≤ (x : ℝ) := by exact Int.floor_le x
      have h3 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
      have h4 : (n : ℝ) ≤ x := by exact_mod_cast h2
      have h5 : x < (n + 1 : ℝ) := by exact_mod_cast h3
      have h6 : 2 * x ^ 2 - (n : ℝ) * x = 5 := by linarith
      have hn : n ≥ 0 := by
        by_contra h
        push_neg at h
        have h7 : n ≤ -1 := by omega
        have h8 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h7
        have h9 : x < (0 : ℝ) := by linarith
        linarith
      have h7 : n ≤ 2 := by
        by_contra h
        push_neg at h
        have h8 : n ≥ 3 := by omega
        have h9 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h8
        nlinarith [Real.sqrt_nonneg 41, Real.sqrt_nonneg 11, heq, Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
      have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases this with (h | h | h)
      · -- n = 0
        have h0 : (n : ℝ) = 0 := by exact_mod_cast h
        rw [h0] at h6
        nlinarith [Real.sqrt_nonneg 41, Real.sqrt_nonneg 11, heq, Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
      · -- n = 1
        have h1 : (n : ℝ) = 1 := by exact_mod_cast h
        rw [h1] at h6
        have h5 : x = (1 + Real.sqrt 41) / 4 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num)]
        left
        linarith
      · -- n = 2
        have h22 : (n : ℝ) = 2 := by exact_mod_cast h
        rw [h22] at h6
        have h25 : x = (1 + Real.sqrt 11) / 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
        right
        linarith
    · -- Show the two given solutions satisfy the original equation
      intro h
      rcases h with (rfl | rfl)
      · -- x = (1 + Real.sqrt 41) / 4
        constructor
        · -- Show x > 0
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sqrt_nonneg 41]
        · -- Show 2 * x ^ 2 - ⌊x⌋ * x = 5
          have h1 : ⌊(1 + Real.sqrt 41) / 4⌋ = 1 := by
            have h2 : 1 ≤ ( (1 + Real.sqrt 41) / 4 : ℝ ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num)]
            have h3 : ( (1 + Real.sqrt 41) / 4 : ℝ ) < 2 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num)]
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> linarith
          rw [h1]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num)]
      · -- x = (1 + Real.sqrt 11) / 2
        constructor
        · -- Show x > 0
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sqrt_nonneg 11]
        · -- Show 2 * x ^ 2 - ⌊x⌋ * x = 5
          have h1 : ⌊(1 + Real.sqrt 11) / 2⌋ = 2 := by
            have h2 : 2 ≤ ( (1 + Real.sqrt 11) / 2 : ℝ ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
            have h3 : ( (1 + Real.sqrt 11) / 2 : ℝ ) < 3 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> linarith
          rw [h1]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  rw [h1]
  rw [finsum_mem_pair]
  field_simp
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  all_goals norm_num
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 41 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 41 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]