import Mathlib

/- A farmer has four sons, whose current ages are denoted by $X_1$, $X_2$, $X_3$, and $X_4$, with the condition that $X_4 \le X_3 \le X_2 \le X_1$ and each age lies between $2$ and $16$ inclusive. One year ago, the ages of the sons satisfied the equation $(X_1-1)^2 = (X_2-1)^2 + (X_3-1)^2 + (X_4-1)^2$. Currently, their ages satisfy the equation $X_1^2 + X_4^2 = X_2^2 + X_3^2$. Determine all possible sets of ages for the four sons. -/
theorem algebra_615798 : {(x1, x2, x3, x4) : ℤ × ℤ × ℤ × ℤ | x4 ≤ x3 ∧ x3 ≤ x2 ∧ x2 ≤ x1 ∧ x4 ≥ 2 ∧ x1 ≤ 16 ∧
  (x1 - 1) ^ 2 = (x2 - 1) ^ 2 + (x3 - 1) ^ 2 +(x4 - 1) ^ 2 ∧ x1 ^ 2 + x4 ^ 2 = x2 ^ 2 + x3 ^ 2} = {(16, 12, 11, 3)} := by
  ext ⟨x1, x2, x3, x4⟩
  constructor
  . -- Forward direction
    rintro ⟨h_34, h32, h21, hmin, hmax, h1, h2⟩
    -- Obtain the relational expression between $x1$ and $x2$, $x3$, $x4$
    have hx1 : x1 = x2 + x3 + x4 - x4 ^ 2 - 1 := by
      have hx1_exp : x1 ^ 2 - 2 * x1 = x2 ^ 2 + x3 ^ 2 + x4 ^ 2 - 2 * x2 - 2 *x3 -2 * x4 + 2 := by nlinarith
      have hx1_sim : x1 ^ 2 = x2 ^ 2 + x3 ^ 2 - x4 ^ 2 := by nlinarith
      rw [hx1_sim] at hx1_exp
      nlinarith
    rw [hx1] at h21
    -- Calculate the range of values for $x4$
    have h34_rel : x4 ^ 2 - x4 + 1 ≤ x3 := by linarith
    have hx4_range : x4 ≤ 4 := by
      have hx4_range_1 : x4 ^ 2 - x4 ≤ 15 := by
        have hx4_range_11 : x4 ^ 2 - x4 + 1 ≤ 16 := by
          have hx3_max : x3 ≤ 16 := by linarith
          apply Int.le_trans h34_rel hx3_max
        linarith
      by_contra hx4f
      push_neg at hx4f
      have h_out : x4 ^ 2 - x4 ≥ 5 ^ 2 - 5:= by
        nlinarith
      linarith
    -- Prove that $x4 = 3$
    have hx4 : x4 = 3 := by
      have hx4_num : x4 = 2 ∨ x4 = 3 ∨ x4 = 4 := by
        interval_cases x4
        all_goals simp
      by_contra hx4_else
      rcases hx4_num with (hx4_2 | hx4_3 | hx4_4)
      . -- Case when $x4 = 2$
        simp [hx4_2] at hx1 h2
        have hx1' : x1 = x2 + x3 - 3 := by linarith
        simp [hx1'] at h2
        have h2_left : (x2 + x3 - 3) ^ 2 = x2 ^ 2 + 2 * x2 * x3 + x3 ^ 2 - 6 * x2 - 6 * x3 + 9 := by ring_nf
        rw [h2_left] at h2
        have h2' : 2 * x2 * x3 - 6 * x2 - 6 * x3 + 13 = 0 := by linarith
        have h2_ring : 2 * (x2 - 3) * (x3 - 3) = 5 := by
          ring_nf
          ring_nf at h2'
          linarith
        have h5even : Even (2 * (x2 - 3) * (x3 - 3)) := by use (x2 - 3) * (x3 - 3); ring
        rw [h2_ring] at h5even
        apply Nat.not_even_bit1 2
        have h5split : 2 * 2 + 1 = (5 : ℤ) := by norm_num
        norm_cast
      . -- Case when $x4 = 3$
        contradiction
      . -- Case when $x4 = 4$
        simp [hx4_4] at hx1 h2
        have hx1' : x1 = x2 + x3 - 13 := by linarith
        rw [hx1'] at h2
        have h2_left : (x2 + x3 - 13) ^ 2 = x2 ^ 2 + 2 * x2 * x3 + x3 ^ 2 - 26 * x2 - 26 * x3 + 169 := by ring_nf
        rw [h2_left] at h2
        have h2' : 2 * x2 * x3 - 26 * x2 - 26 * x3 + 185 = 0 := by linarith
        have h2_ring : 2 * (x2 - 13) * (x3 - 13) = 153 := by
          ring_nf
          ring_nf at h2'
          linarith
        have h153even : Even (2 * (x2 - 13) * (x3 - 13)) := by use (x2 - 13) * (x3 - 13); ring
        rw [h2_ring] at h153even
        apply Nat.not_even_bit1 153
        have h153split : 2 * 76 + 1 = (153 : ℤ) := by norm_num
        norm_cast
    simp [hx4] at hx1 h2 h34_rel
    have h2_ring : (x2 - 7) * (x3 - 7) = 20 := by
      have hx1' : x1 = x2 + x3 - 7 := by linarith
      rw [hx1'] at h2
      have h2_left : (x2 + x3 - 7) ^ 2 = x2 ^ 2 + 2 * x2 * x3 + x3 ^ 2 - 14 * x2 - 14 * x3 + 49 := by ring_nf
      rw [h2_left] at h2
      have h2' : x2 * x3 - 7 * x2 - 7 * x3 + 29 = 0 := by linarith
      ring_nf at h2'
      linarith
    have hx2_range_1 : x2 - 7 ≤ 9 := by linarith
    have hx2_range_2 : 0 ≤ x2 - 7 := by linarith
    -- Prove that $x2 - 7 = 5$
    have hx2' : x2 - 7 = 5 := by
      by_contra hx2f
      have hx2_else : x2 - 7 = 0 ∨ x2 - 7 = 1 ∨ x2 - 7 = 2 ∨ x2 - 7 = 3 ∨ x2 - 7 = 4 ∨ x2 - 7 = 6 ∨ x2 - 7 = 7 ∨ x2 - 7 = 8 ∨ x2 - 7 = 9 := by
        interval_cases (x2 - 7)
        all_goals simp
        norm_num at hx2f
      rcases hx2_else with (hx | hx | hx | hx | hx | hx | hx | hx | hx)
      all_goals try simp [hx] at h2_ring
      all_goals linarith
    -- Prove that $x2 = 12$
    have hx2 : x2 = 12 := by linarith
    -- Prove that $x3 = 11$
    have hx3 : x3 = 11 := by
      have hx3' : x3 - 7 = 4 := by
        simp [hx2] at h2_ring
        linarith
      linarith
    -- Prove that $x1 = 16$
    have hx1 : x1 = 16 := by
      rw [hx2, hx3] at hx1
      linarith
    simp_all
  . -- Backward direction
    simp_all