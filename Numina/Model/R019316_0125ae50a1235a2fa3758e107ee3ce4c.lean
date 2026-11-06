import Mathlib

theorem algebra_243301 : Set.ncard {z : ℝ | ∃ x y, x * y ≠ 0 ∧ z = x / abs x + y / abs y + x * y / abs (x * y)} = 2 := by
  have h1 : {z : ℝ | ∃ x y, x * y ≠ 0 ∧ z = x / abs x + y / abs y + x * y / abs (x * y)} = {-1, 3} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: all expressions in the set
      rintro ⟨x, y, hxy, hz⟩
      have hx1 : x ≠ 0 := by
        by_contra h
        rw [h] at hxy
        simp [h] at hxy
      have hy1 : y ≠ 0 := by
        by_contra h
        rw [h] at hxy
        simp [h] at hxy
      have h2 : x / abs x = 1 ∨ x / abs x = -1 := by
        cases (le_or_lt 0 x) with
        | inl h3 =>
          have hx2 : abs x = x := by
            rw [abs_of_nonneg h3]
          have hx3 : x > 0 := by
            by_contra h
            push_neg at h
            have hx4 : x ≤ 0 := by linarith
            have hx5 : x < 0 := by
                by_contra h
                push_neg at h
                have hx6 : x = 0 := by linarith
                contradiction
            linarith
          rw [hx2]
          left
          field_simp [show x ≠ 0 by assumption]
        | inr h3 =>
          have hx2 : abs x = -x := by
            rw [abs_of_neg h3]
          have hx3 : x < 0 := by linarith
          rw [hx2]
          right
          field_simp [show x ≠ 0 by assumption]
      have h3 : y / abs y = 1 ∨ y / abs y = -1 := by
        cases (le_or_lt 0 y) with
        | inl h3 =>
          have hy2 : abs y = y := by
            rw [abs_of_nonneg h3]
          have hy3 : y > 0 := by
            by_contra h
            push_neg at h
            have hy4 : y ≤ 0 := by linarith
            have hy5 : y < 0 := by
                by_contra h
                push_neg at h
                have hy6 : y = 0 := by linarith
                contradiction
            linarith
          rw [hy2]
          left
          field_simp [show y ≠ 0 by assumption]
        | inr h3 =>
          have hy2 : abs y = -y := by
            rw [abs_of_neg h3]
          have hy3 : y < 0 := by linarith
          rw [hy2]
          right
          field_simp [show y ≠ 0 by assumption]
      have h4 : x * y / abs (x * y) = (x / abs x) * (y / abs y) := by
        have h5 : abs (x * y) = abs x * abs y := by
          rw [abs_mul]
        rw [h5]
        have hx2 : x ≠ 0 := by assumption
        have hy2 : y ≠ 0 := by assumption
        field_simp [show abs x ≠ 0 by
          by_contra h
          have : abs x = 0 := by linarith
          have h6 : x = 0 := abs_eq_zero.mp this
          contradiction
          , show abs y ≠ 0 by
            by_contra h
            have : abs y = 0 := by linarith
            have h6 : y = 0 := abs_eq_zero.mp this
            contradiction
          , hx2, hy2
        ]
        <;> ring_nf <;> norm_num
      rw [h4] at hz
      rcases h2 with (hx2 | hx2)
      <;> rcases h3 with (hy3 | hy3)
      <;> 
        try { 
          have h5 : z = 3 := by 
            nlinarith [hz, hx2, hy3]
          rw [h5]
          all_goals norm_num 
        }
      <;> try { 
        have h5 : z = -1 := by 
          nlinarith [hz, hx2, hy3]
        rw [h5]
        all_goals norm_num 
      }
    · -- Second direction, {-1, 3} in the set
      rintro (rfl | rfl)
      · -- When z = -1
        use 1, -1
        norm_num [abs_of_pos, abs_of_neg, mul_neg, abs_neg]
      · -- When z = 3
        use 1, 1
        norm_num [abs_of_pos, abs_of_neg, mul_pos]
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]