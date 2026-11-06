import Mathlib
/-Find all solutions of the equation x^2-12[x]+20=0 -/
theorem algebra_113079 (x : ℝ) :
    x^2 - 12 * ⌊x⌋ + 20 = 0 ↔ x = 2 ∨ x = 2 * Real.sqrt 19 ∨ x = 2 * Real.sqrt 22 ∨ x = 10 := by
  constructor
  · -- Assume x^2 - 12 * ⌊x⌋ + 20 = 0, we need to prove x = 2 ∨ x = 2 * sqrt 19 ∨ x = 2 * sqrt 22 ∨ x = 10
    intro h
    let n := ⌊x⌋
    have hn : n = ⌊x⌋ := by rfl
    have h1 : (n : ℝ) = ⌊x⌋ := by exact_mod_cast rfl
    have h2 : x^2 + 20 = 12 * (n : ℝ) := by linarith
    have h3 : (n : ℝ) ≤ x := Int.floor_le x
    have h4 : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
    have h5 : (n : ℝ) ^ 2 ≤ 12 * (n : ℝ) - 20 := by nlinarith [sq_nonneg (x - (n : ℝ)), h2]
    have h6 : 12 * (n : ℝ) - 20 < ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (x - (n : ℝ)), h2, h4]
    have h7 : 2 ≤ (n : ℝ) := by
      nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) - 10), h5]
    have h8 : (n : ℝ) ≤ 10 := by -- this gives the key upper bound
      nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) - 10), h5]
    have h9 : (n : ℝ) < 3 ∨ (n : ℝ) > 7 := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg ((n : ℝ) - 3), sq_nonneg ((n : ℝ) - 7), h6]
    have hn2 : n ≥ 2 := by
      by_contra h
      push_neg at h
      have h10 : (n : ℝ) < 2 := by
        exact_mod_cast h
      linarith
    have hn10 : n ≤ 10 := by
      by_contra h
      push_neg at h
      have h11 : (n : ℝ) > 10 := by
        exact_mod_cast h
      linarith
    have h12 : n < 3 ∨ n > 7 := by
      cases h9 with
      | inl h13 =>
        left
        by_contra h14
        push_neg at h14
        have h15 : (n : ℝ) ≥ 3 := by
          exact_mod_cast h14
        linarith
      | inr h16 =>
        right
        by_contra h17
        push_neg at h17
        have h18 : (n : ℝ) ≤ 7 := by
          exact_mod_cast h17
        linarith  -- now check all cases
    have h_n : n = 2 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by
      omega
    rcases h_n with hn2 | hn8 | hn9 | hn10
    · -- n = 2
      have hn2' : (n : ℝ) = (2 : ℝ) := by exact_mod_cast hn2
      have h_eq : x^2 = 4 := by
        rw [hn2'] at h2
        nlinarith
      have h_floor_2 : 2 ≤ x := by
        rw [hn2'] at h3
        linarith
      have h_floor_3 : x < 3 := by
        rw [hn2'] at h4
        linarith
      have h_x : x = 2 := by
        have h1 : x^2 - 4 = 0 := by linarith
        have h2 : (x - 2) * (x + 2) = 0 := by
          ring_nf at h1 ⊢
          linarith
        cases' (mul_eq_zero.mp h2) with h3 h4
        · -- x - 2 = 0
          linarith
        · -- x + 2 = 0
          have h5 : x = -2 := by linarith
          linarith [h5, h_floor_2]
      left
      exact h_x
    · -- n = 8
      have hn8' : (n : ℝ) = (8 : ℝ) := by exact_mod_cast hn8
      have h_eq : x^2 = 76 := by
        rw [hn8'] at h2
        nlinarith
      have h_floor_8 : 8 ≤ x := by
        rw [hn8'] at h3
        linarith
      have h_floor_9 : x < 9 := by
        rw [hn8'] at h4
        linarith
      have h_x_pos : 0 ≤ x := by nlinarith [h_floor_8]
      have hx : x = Real.sqrt 76 := by
        rw [←h_eq]
        field_simp [h_x_pos]
      have hx2 : x = 2 * Real.sqrt 19 := by
        rw [hx]
        have h : Real.sqrt 76 = 2 * Real.sqrt 19 := by
          calc
            Real.sqrt 76 = Real.sqrt (2^2 * 19) := by norm_num
            _ = Real.sqrt (2^2) * Real.sqrt 19 := by rw [Real.sqrt_mul (by norm_num)]
            _ = 2 * Real.sqrt 19 := by rw [Real.sqrt_sq (by norm_num)]
        exact h
      right
      left
      exact hx2
    · -- n = 9
      have hn9' : (n : ℝ) = (9 : ℝ) := by exact_mod_cast hn9
      have h_eq : x^2 = 88 := by
        rw [hn9'] at h2
        nlinarith
      have h_floor_9 : 9 ≤ x := by
        rw [hn9'] at h3
        linarith
      have h_floor_10 : x < 10 := by
        rw [hn9'] at h4
        linarith
      have h_x_pos : 0 ≤ x := by nlinarith [h_floor_9]
      have hx : x = Real.sqrt 88 := by
        rw [←h_eq]
        field_simp [h_x_pos]
      have hx2 : x = 2 * Real.sqrt 22 := by
        rw [hx]
        have h : Real.sqrt 88 = 2 * Real.sqrt 22 := by
          calc
            Real.sqrt 88 = Real.sqrt (2^2 * 22) := by norm_num
            _ = Real.sqrt (2^2) * Real.sqrt 22 := by rw [Real.sqrt_mul (by norm_num)]
            _ = 2 * Real.sqrt 22 := by rw [Real.sqrt_sq (by norm_num)]
        exact h
      right
      right
      left
      exact hx2
    · -- n = 10
      have hn10' : (n : ℝ) = (10 : ℝ) := by exact_mod_cast hn10
      have h_eq : x^2 = 100 := by
        rw [hn10'] at h2
        nlinarith
      have h_floor_10 : 10 ≤ x := by
        rw [hn10'] at h3
        linarith
      have h_floor_11 : x < 11 := by
        rw [hn10'] at h4
        linarith
      have h_x : x = 10 := by
        have h1 : x^2 - 100 = 0 := by linarith
        have h2 : (x - 10) * (x + 10) = 0 := by
          ring_nf at h1 ⊢
          linarith
        cases' (mul_eq_zero.mp h2) with h3 h4
        · -- x - 10 = 0
          linarith
        · -- x + 10 = 0
          have h5 : x = -10 := by linarith
          linarith [h5, h_floor_10]
      right
      right
      right
      exact h_x
  · -- Assume x = 2 ∨ x = 2 * sqrt 19 ∨ x = 2 * sqrt 22 ∨ x = 10, prove x^2 - 12 * ⌊x⌋ + 20 = 0
    rintro (rfl | rfl | rfl | rfl)
    · -- x = 2
      norm_num
    · -- x = 2 * sqrt 19
      have h1 : (2 * Real.sqrt 19) ^ 2 = 76 := by
        calc
          (2 * Real.sqrt 19) ^ 2 = 4 * (Real.sqrt 19 * Real.sqrt 19) := by ring
          _ = 4 * 19 := by rw [Real.mul_self_sqrt]; norm_num
          _ = 76 := by norm_num
      have h2 : ⌊2 * Real.sqrt 19⌋ = 8 := by
        have h3 : 2 * Real.sqrt 19 < 9 := by
          have h4 : Real.sqrt 19 < 4.5 := by
            rw [Real.sqrt_lt] <;> norm_num
          nlinarith [h4]
        have h5 : 8 ≤ 2 * Real.sqrt 19 := by
          have h6 : 4 ≤ Real.sqrt 19 := by
            rw [Real.le_sqrt] <;> norm_num
          nlinarith [h6]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> linarith
      rw [h1, h2]
      all_goals norm_num
    · -- x = 2 * sqrt 22
      have h1 : (2 * Real.sqrt 22) ^ 2 = 88 := by
        calc
          (2 * Real.sqrt 22) ^ 2 = 4 * (Real.sqrt 22 * Real.sqrt 22) := by ring
          _ = 4 * 22 := by rw [Real.mul_self_sqrt]; norm_num
          _ = 88 := by norm_num
      have h2 : ⌊2 * Real.sqrt 22⌋ = 9 := by
        have h3 : 2 * Real.sqrt 22 < 10 := by
          have h4 : Real.sqrt 22 < 5 := by
            rw [Real.sqrt_lt] <;> norm_num
          nlinarith [h4]
        have h5 : 9 ≤ 2 * Real.sqrt 22 := by
          have h6 : 4.5 ≤ Real.sqrt 22 := by
            rw [Real.le_sqrt] <;> norm_num
          nlinarith [h6]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> linarith
      rw [h1, h2]
      all_goals norm_num
    · -- x = 10
      norm_num