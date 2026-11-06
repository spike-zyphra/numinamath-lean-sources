import Mathlib

theorem algebra_218947 :
    {x : ℝ | -15 ≤ x ∧ x ≤ 2 ∧ (2 - x) ^ ((1 : ℝ) / 4) + (15 + x) ^ ((1 : ℝ) / 4) = 3} = {-14, 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the left side, prove in the right
    rintro ⟨hx1, hx2, heq⟩
    have h1 : (2 - x : ℝ) ^ ((1 : ℝ) / 4) + (15 + x : ℝ) ^ ((1 : ℝ) / 4) = 3 := by linarith
    have h2 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 - x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h3 : ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 15 + x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h4 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 + ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 17 := by
      have h5 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 - x := h2
      have h6 : ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 15 + x := h3
      nlinarith
    have h5 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) = 1 ∨ ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) = 2 := by
      have h6 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) + ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) = 3 := h1
      have h7 : ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 + ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 17 := h4
      have h8 : ((15 + x : ℝ) ^ ((1 : ℝ) / 4)) = 3 - ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) := by linarith
      rw [h8] at h7
      have h9 : ( ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ) ^ 4 + ( (3 - ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ) ) ^ 4 = 17 := by linarith
      have h10 : ( ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) - 1 ) * ( ( ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ) - 2 ) = 0 := by 
        nlinarith [sq_nonneg ((2 - x : ℝ) ^ ((1 : ℝ) / 4) - 1), sq_nonneg ((2 - x : ℝ) ^ ((1 : ℝ) / 4) - 2), sq_nonneg ((2 - x : ℝ) ^ ((1 : ℝ) / 4) + (15 + x : ℝ) ^ ((1 : ℝ) / 4) - 3), sq_nonneg ((2 - x : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - 3 * ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) + 2)]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- Case $A - 1 = 0$, so $A = 1$
        left
        linarith
      · -- Case $A - 2 = 0$, so $A = 2$
        right
        linarith
    cases h5 with
    | inl h6 =>
      -- Case $A = 1$, prove $x = 1$
      have h7 : (2 - x : ℝ) ^ ((1 : ℝ) / 4) = 1 := h6
      have : 2 - x = 1 := by
        calc
          2 - x = ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by 
            rw [h2]
          _ = (1) ^ 4 := by 
            rw [h7]
          _ = (1 : ℝ) := by norm_num
      have : x = 1 := by linarith
      right
      tauto
    | inr h6 =>
      -- Case $A = 2$, prove $x = -14$
      have h7 : (2 - x : ℝ) ^ ((1 : ℝ) / 4) = 2 := h6
      have : 2 - x = 16 := by
        calc
          2 - x = ((2 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by 
            rw [h2]
          _ = (2) ^ 4 := by 
            rw [h7]
          _ = (16 : ℝ) := by norm_num
      have : x = -14 := by linarith
      left
      tauto
  · -- Assume x in the right side, prove in the left
    rintro (h | h)
    · -- Case x = -14
      have hx1 : x = -14 := by linarith
      rw [hx1]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that the equation is satisfied 
        have h1 : (2 - (-14 : ℝ)) ^ ((1 : ℝ) / 4) = 2 := by
          have h2 : (2 - (-14 : ℝ)) ^ ((1 : ℝ) / 4) = (16 : ℝ) ^ ((1 : ℝ) / 4) := by 
            norm_num
          rw [h2]
          have h3 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          linarith
        have h4 : (15 + (-14 : ℝ)) ^ ((1 : ℝ) / 4) = 1 := by
          have h5 : (15 + (-14 : ℝ)) ^ ((1 : ℝ) / 4) = (1 : ℝ) ^ ((1 : ℝ) / 4) := by 
            norm_num
          rw [h5]
          have h6 : (1 : ℝ) ^ ((1 : ℝ) / 4) = (1 : ℝ) := by 
            simp
          linarith
        rw [h1, h4]
        all_goals norm_num
    · -- Case x = 1
      have hx1 : x = 1 := by linarith
      rw [hx1]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that the equation is satisfied 
        have h1 : (2 - (1 : ℝ)) ^ ((1 : ℝ) / 4) = 1 := by
          have h2 : (2 - (1 : ℝ)) ^ ((1 : ℝ) / 4) = (1 : ℝ) ^ ((1 : ℝ) / 4) := by 
            norm_num
          rw [h2]
          have h3 : (1 : ℝ) ^ ((1 : ℝ) / 4) = (1 : ℝ) := by 
            simp
          linarith
        have h4 : (15 + (1 : ℝ)) ^ ((1 : ℝ) / 4) = 2 := by
          have h5 : (15 + (1 : ℝ)) ^ ((1 : ℝ) / 4) = (16 : ℝ) ^ ((1 : ℝ) / 4) := by 
            norm_num
          rw [h5]
          have h6 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          linarith
        rw [h1, h4]
        all_goals norm_num