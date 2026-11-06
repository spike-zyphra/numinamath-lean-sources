import Mathlib

theorem algebra_106125 : {x : ℝ | x^2 - 4 * ⌊x⌋ + 3 = 0}.encard = 3 := by
  have h1 : {x : ℝ | x^2 - 4 * ⌊x⌋ + 3 = 0} = {1, Real.sqrt 5, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x^2 - 4⌊x⌋ + 3 = 0, prove {1, sqrt 5, 3}
      intro h
      have h_eq : x^2 = 4 * (⌊x⌋ : ℝ) - 3 := by linarith
      have h2 : ⌊x⌋ ≤ (x : ℝ) := by exact Int.floor_le x
      have h3 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
      have h4 : ⌊x⌋ ≤ 3 := by
        by_contra h4
        push_neg at h4
        have h5 : ⌊x⌋ ≥ 4 := by omega
        have h5' : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h5
        have h6 : x ≥ (4 : ℝ) := by linarith [h2, h5']
        nlinarith [sq_nonneg (x - (4 : ℝ)), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x - (⌊x⌋ : ℝ) - 1)]
      have h8 : ⌊x⌋ ≥ 1 := by
        by_contra h8
        push_neg at h8
        have h9 : ⌊x⌋ ≤ 0 := by omega
        have h9' : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h9
        nlinarith [sq_nonneg (x - (0 : ℝ)), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x - (⌊x⌋ : ℝ) - 1)]
      have h5 : ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 := by omega
      rcases h5 with (h_eq1 | h_eq2 | h_eq3)
      · -- When ⌊x⌋ = 1
        have h14 : (⌊x⌋ : ℝ) = 1 := by exact_mod_cast h_eq1
        rw [h14] at h_eq
        have h27 : x ^ 2 = (1 : ℝ) := by linarith
        have h12 : x = 1 ∨ x = -1 := by
          have h14 : x ^ 2 = 1 := h27
          have h13 : x = 1 ∨ x = -1 := by
            rw [sq_eq_one_iff] at h14
            assumption
          assumption
        rcases h12 with (r | r)
        · -- x = 1
          left
          linarith
        · -- x = -1
          nlinarith
      · -- When ⌊x⌋ = 2
        have h14 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h_eq2
        rw [h14] at h_eq
        have h27 : x ^ 2 = (5 : ℝ) := by linarith
        have h15 : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
          have h14 : x ^ 2 = (5 : ℝ) := h27
          have h17 : x^2 = (Real.sqrt 5) ^ 2 := by
            rw [h14]
            rw [Real.sq_sqrt]
            all_goals norm_num
          have h18 : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
            have : x^2 = (Real.sqrt 5) ^ 2 := h17
            have : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
              have h : x ^ 2 = (Real.sqrt 5) ^ 2 := this
              have : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
                rw [sq_eq_sq_iff_eq_or_eq_neg] at h
                tauto
              assumption
            assumption
          assumption
        rcases h15 with (r | r)
        · -- x = Real.sqrt 5
          right
          left
          linarith
        · -- x = -Real.sqrt 5
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
      · -- When ⌊x⌋ = 3
        have h14 : (⌊x⌋ : ℝ) = (3 : ℝ) := by exact_mod_cast h_eq3
        rw [h14] at h_eq
        have h27 : x ^ 2 = (9 : ℝ) := by linarith
        have h12 : x = 3 ∨ x = -3 := by
          have h14 : x ^ 2 = 9 := by linarith
          have h15 : x ^ 2 - 9 = 0 := by linarith
          have h16 : (x - 3) * (x + 3) = 0 := by nlinarith
          cases' (mul_eq_zero.mp h16) with h17 h18
          · -- Case $x - 3 = 0$, so $x = 3$.
            left
            linarith
          · -- Case $x + 3 = 0$, so $x = -3$.
            right
            linarith
        rcases h12 with (r | r)
        · -- x = 3
          right
          right
          linarith
        · -- x = -3
          nlinarith
    · -- Assume x ∈ {1, sqrt 5, 3}, prove x^2 - 4⌊x⌋ + 3 = 0
      rintro (rfl | rfl | rfl)
      · -- When x = 1
        norm_num
      · -- When x = Real.sqrt 5
        have h10 : ⌊Real.sqrt 5⌋ = 2 := by
          have h11 : 2 < Real.sqrt 5 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h12 : Real.sqrt 5 < (3 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          have h10 : ⌊Real.sqrt 5⌋ = 2 := by
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
          assumption
        have h27 : (⌊Real.sqrt 5⌋ : ℝ) = 2 := by exact_mod_cast h10
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      · -- When x = 3
        norm_num
  rw [h1]
  have h2 : Real.sqrt 5 > (1 : ℝ) := by
    have h1 : Real.sqrt 5 > Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    have h2 : Real.sqrt 1 = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    nlinarith
  have h3 : Real.sqrt 5 < (3 : ℝ) := by
    have h4 : Real.sqrt 5 < (3 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    linarith
  have h4 : (1 : ℝ) < Real.sqrt 5 := h2
  have h5 : Real.sqrt 5 < (3 : ℝ) := h3
  have h12 : (1 : ℝ) ≠ Real.sqrt 5 := by linarith
  have h13 : (1 : ℝ) ≠ (3 : ℝ) := by linarith
  have h14 : Real.sqrt 5 ≠ (3 : ℝ) := by linarith
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton, h12, h13, h14]
  all_goals norm_num