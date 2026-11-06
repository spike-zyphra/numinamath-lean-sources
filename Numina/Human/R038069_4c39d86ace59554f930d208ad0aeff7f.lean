import Mathlib

/-if the equation |2x-3|+m=0 has no solution, |3x-4|+n=0 has only one solution, and |4x-5|+k has two solutions, then the relationship of the size of m,n,k is -/
theorem algebra_2125 (m n k : ℝ) (h₀ : ¬∃ x, abs (2 * x - 3) + m = 0)
    (h₁ : ∃! x, abs (3 * x - 4) + n = 0) (h₂ : ∃ x y, x ≠ y ∧ abs (4 * x - 5) + k = 0 ∧
    abs (4 * y - 5) + k = 0) : m > n ∧ n > k := by
-- show m>0
  have h0 : m > 0 := by
    by_contra h
    push_neg at h
    have h' : ∃ x, abs (2 * x - 3) + m = 0 := by
      use (3 - m) / 2
      rw [show 2 * ((3 - m) / 2) - 3 = -m by ring]
      rw [abs_of_nonneg (by linarith)]
      linarith
    contradiction
-- show n=0
  have h1 : n = 0 := by
    rcases h₁ with ⟨x, hx1, hx2⟩
    have hn1 : n ≤ 0 := by
      have h_abs_nonneg : abs (3 * x - 4) ≥ 0 := abs_nonneg (3 * x - 4)
      linarith [hx1, h_abs_nonneg]
    have hn2 : n ≥ 0 := by
      by_contra h
      push_neg at h
      have h_eq : abs (3 * x - 4) = -n := by linarith [hx1]
      have h2 : 3 * x - 4 = -n ∨ 3 * x - 4 = n := by
        cases eq_or_eq_neg_of_abs_eq h_eq with
        | inl h1 => left; linarith
        | inr h2 => right; linarith
      cases h2 with
      | inl h2l =>
        have y_val : ∃ y, y ≠ x ∧ abs (3 * y - 4) + n = 0 := by
          use (4 + n) / 3
          have hy1 : (4 + n) / 3 ≠ x := by
            intro h
            have hx_eq : x = (4 - n) / 3 := by
              linarith
            rw [hx_eq] at h
            have h' : n = 0 := by
              linarith
            linarith
          constructor
          · exact hy1
          · have h_abs : abs (3 * ((4 + n) / 3) - 4) + n = 0 := by
              have h : abs (3 * ((4 + n) / 3) - 4) = abs n := by
                simp [abs]
                ring_nf
              rw [h]
              have h_abs_n : abs n = -n := by
                rw [abs_of_nonpos]
                linarith
              linarith [h_abs_n]
            linarith [h_abs]
        obtain ⟨y, hy1, hy2⟩ := y_val
        have h_unique := hx2 y hy2
        contradiction
      | inr h2r =>
        have y_val : ∃ y, y ≠ x ∧ abs (3 * y - 4) + n = 0 := by
          use (4 - n) / 3
          have hy1 : (4 - n) / 3 ≠ x := by
            intro h
            have hx_eq : x = (4 + n) / 3 := by
              linarith
            rw [hx_eq] at h
            have h' : n = 0 := by
              linarith
            linarith
          constructor
          · exact hy1
          · have h_abs : abs (3 * ((4 - n) / 3) - 4) + n = 0 := by
              have h : abs (3 * ((4 - n) / 3) - 4) = abs (-n) := by
                simp [abs]
                ring_nf             
              rw [h]
              have h_abs_n : abs (-n) = -n := by
                rw [abs_of_pos]
                linarith
              linarith [h_abs_n]
            linarith [h_abs]
        obtain ⟨y, hy1, hy2⟩ := y_val
        have h_unique := hx2 y hy2
        contradiction
    linarith
-- show k<0
  have h2 : k < 0 := by
    rcases h₂ with ⟨x, y, hxy, hx, hy⟩
    by_contra h
    push_neg at h
    have h_k : k = 0 := by
      have h_abs_nonneg_x : abs (4 * x - 5) ≥ 0 := abs_nonneg (4 * x - 5)
      have h_abs_nonneg_y : abs (4 * y - 5) ≥ 0 := abs_nonneg (4 * y - 5)
      have h1 : abs (4 * x - 5) = -k := by linarith
      have h2 : abs (4 * y - 5) = -k := by linarith
      have h3 : -k ≥ 0 := by linarith [h_abs_nonneg_x, h1]
      have h4 : -k ≤ 0 := by linarith
      linarith
    rw [h_k] at hx hy
    have hx_eq : abs (4 * x - 5) = 0 := by linarith
    have hy_eq : abs (4 * y - 5) = 0 := by linarith
    have hx_eq2 : 4 * x - 5 = 0 := abs_eq_zero.mp hx_eq
    have hy_eq2 : 4 * y - 5 = 0 := abs_eq_zero.mp hy_eq
    have hx_eq3 : x = 5 / 4 := by
      linarith
    have hy_eq3 : y = 5 / 4 := by
      linarith
    rw [hx_eq3, hy_eq3] at hxy
    contradiction
  
  constructor
  · linarith [h0, h1]
  · linarith [h1, h2]