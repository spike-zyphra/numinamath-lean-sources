import Mathlib

theorem algebra_186601 {x : ℝ} (hx : x ≠ -1) (h : 1 / (x * (x + 2)) - 1 / (x + 1) ^ 2 = 1 / 12) :
    x = -3 ∨ x = 1 := by
  have h1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at h
    norm_num at h
    all_goals try { tauto }
  have h2 : x + 1 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h3 : x + 2 ≠ 0 := by
    by_contra h4
    have h4' : x = -2 := by linarith
    rw [h4'] at h
    norm_num at h
  have eq1 : 1 / (x * (x + 2)) - 1 / (x + 1) ^ 2 = ((x + 1) ^ 2 - x * (x + 2)) / (x * (x + 2) * (x + 1) ^ 2) := by
    field_simp [h1, h2, h3]
    <;> ring_nf <;> field_simp [h1, h2, h3] <;> ring
  have eq2 : (x + 1) ^ 2 - x * (x + 2) = 1 := by
    nlinarith
  have eq3 : 1 / (x * (x + 2) * (x + 1) ^ 2) = 1 / 12 := by
    have eq4 : 1 / (x * (x + 2)) - 1 / (x + 1) ^ 2 = 1 / (x * (x + 2) * (x + 1) ^ 2) := by
      rw [eq1]
      rw [eq2]
      all_goals norm_num
    linarith [h, eq4]
  have eq4 : x * (x + 1) ^ 2 * (x + 2) = 12 := by
    have hne : x * (x + 1) ^ 2 * (x + 2) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      · exact h1
      · exact pow_ne_zero 2 (show x + 1 ≠ 0 by exact h2)
      · exact h3
    field_simp [hne] at eq3 ⊢ 
    nlinarith [sq_pos_of_ne_zero (show x * (x + 1) ^ 2 * (x + 2) ≠ 0 by exact hne)]
  have eq5 : (x + 3) * (x - 1) = 0 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x + 1) ^ 2), sq_nonneg ((x + 2) ^ 2)]
  cases' (mul_eq_zero.mp eq5) with h6 h7 
  · -- Case where $x + 3 = 0$, so $x = -3$
    left 
    linarith 
  · -- Case where $x - 1 = 0$, so $x = 1$
    right 
    linarith