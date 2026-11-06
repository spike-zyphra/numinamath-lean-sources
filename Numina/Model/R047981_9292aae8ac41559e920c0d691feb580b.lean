import Mathlib

theorem algebra_14787 :
  {k : ℝ | ∃ x y, x ≠ y ∧ 5*x^2+4*x+k=0 ∧ 5*y^2+4*y+k=0 ∧ |x-y| = x^2+y^2} = {3/5, -12/5} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume there are two distinct solutions x and y
    rintro ⟨x, y, hxy, hx, hy, h⟩
    have h1 : x - y ≠ 0 := by
      intro h2
      have : x = y := by linarith
      contradiction
    have eq1 : 5 * (x ^ 2 - y ^ 2) + 4 * (x - y) = 0 := by
      nlinarith
    have eq2 : x + y = -4 / 5 := by
      have h2 : x - y ≠ 0 := h1
      have eq3 : 5 * (x + y) + 4 = 0 := by
        apply (mul_left_inj' (show x - y ≠ 0 by exact h2)).mp
        linarith
      linarith
    -- Now compute $xy$.
    have eq3 : x * y = k / 5 := by
      nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by exact h1), sq_nonneg (x - y), sq_nonneg (x + y)]
    have h2 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      nlinarith
    have eq4 : (x - y) ^ 2 = 16 / 25 - 4 * k / 5 := by
      rw [h2, eq2, eq3]
      linarith
    have eq5 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      nlinarith
    have eq6 : x ^ 2 + y ^ 2 = 16 / 25 - 2 * k / 5 := by
      rw [eq5, eq2, eq3]
      linarith
    have eq7 : (x - y) ^ 2 = (x ^ 2 + y ^ 2) ^ 2 := by
      have h2 : |x - y| = x ^ 2 + y ^ 2 := by
        linarith [h]
      have h3 : 0 ≤ x - y ∨ 0 ≤ -(x - y) := by
        by_contra h
        push_neg at h
        have : x < y := by linarith [h]
        have : x - y < 0 := by linarith
        have h4 : |x - y| = -(x - y) := by
          apply abs_of_neg
          all_goals linarith
        rw [h4] at h2
        nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - (-(x - y))), sq_nonneg (x - y), sq_nonneg (x + y)]
      cases h3 with
      | inl h01 =>
        have h4 : |x - y| = (x - y) := by
          rw [abs_of_nonneg h01]
        rw [h4] at h2
        nlinarith [sq_nonneg (x - y), sq_nonneg ((x ^ 2 + y ^ 2) - (x - y)), sq_nonneg (x + y)]
      | inr h02 =>
        have h5 : |x - y| = -(x - y) := by
          rw [abs_of_nonpos (by linarith)]
        rw [h5] at h2
        nlinarith [sq_nonneg (x - y), sq_nonneg ((x ^ 2 + y ^ 2) + (x - y)), sq_nonneg (x + y)]
    rw [eq4, eq6] at eq7
    have eq8 : 25 * k ^ 2 + 45 * k - 36 = 0 := by
      nlinarith
    have eq9 : (k - 3 / 5) * (k + 12 / 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq9) with eq10 eq11
    · 
      left 
      linarith
    · 
      right 
      linarith
  · -- Show that both k work
    intro h
    rcases h with (r | r)
    · 
      rw [r]
      use -1 / 5, -3 / 5 
      constructor
      · -- Show they are different 
        norm_num 
      constructor
      · -- Check first root 
        norm_num 
      constructor
      · -- Check second root 
        norm_num 
      · -- Check difference equals square of the roots sum 
        norm_num [abs]
    · 
      rw [r]
      use 2 / 5, -6 / 5 
      constructor
      · -- Show they are different 
        norm_num 
      constructor
      · -- Check first root 
        norm_num 
      constructor
      · -- Check second root 
        norm_num 
      · -- Check difference equals square of the roots sum 
        norm_num [abs]