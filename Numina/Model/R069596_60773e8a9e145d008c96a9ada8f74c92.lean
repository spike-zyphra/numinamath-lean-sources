import Mathlib

theorem algebra_162540 (p : ℝ) (h : ∃ r, (3 * p + 1) = r * (|p - 3|) ∧ (9 * p + 10) = r * (3 * p + 1)) :
    p = -1 ∨ p = 29 / 18 := by
  rcases h with ⟨r, ⟨h₁, h₂⟩⟩
  by_cases h3 : p ≥ 3
  · -- Case where p ≥ 3, so |p - 3| = p - 3
    have h4 : |p - 3| = p - 3 := by
      rw [abs_of_nonneg]
      linarith
      all_goals norm_num
    rw [h4] at h₁
    by_cases h3' : p > 3
    · -- Case where p > 3
      have h5 : r = (3 * p + 1) / (p - 3) := by
        have ne1 : p - 3 ≠ 0 := by
          nlinarith
        field_simp [ne1]
        <;> nlinarith
      rw [h5] at h₂
      have h6 : (9 * p + 10) * (p - 3) = (3 * p + 1) ^ 2 := by
        have ne1 : p - 3 ≠ 0 := by
          nlinarith
        field_simp [ne1] at h₂ ⊢
        <;> nlinarith
      nlinarith [sq_nonneg (p - 3 / 1), sq_nonneg (9 * p + 10)]
    · -- Case where p = 3
      have h4' : p = 3 := by
        linarith
        all_goals nlinarith
      rw [h4'] at h₁ h₂
      norm_num at h₁ h₂
      all_goals nlinarith
  · -- Case where p < 3, so |p - 3| = 3 - p
    have h4 : |p - 3| = 3 - p := by
      rw [abs_of_neg (show (p - 3 : ℝ) < 0 by linarith)]
      all_goals linarith
    rw [h4] at h₁
    have eq2 : (9 * p + 10) * (3 - p) = (3 * p + 1) ^ 2 := by
      have h5 : r = (3 * p + 1) / (3 - p) := by
        have ne1 : 3 - p ≠ 0 := by
          linarith
          all_goals nlinarith
        field_simp [ne1]
        <;> nlinarith
      rw [h5] at h₂
      have h6 : (9 * p + 10) * (3 - p) = (3 * p + 1) ^ 2 := by
        have ne1 : 3 - p ≠ 0 := by
          linarith
          all_goals nlinarith
        field_simp [ne1] at h₂ ⊢
        <;> nlinarith
      nlinarith
    have eq3 : 18 * p ^ 2 - 11 * p - 29 = 0 := by
      have h10 : (9 * p + 10) * (3 - p) - (3 * p + 1) ^ 2 = 0 := by
        linarith [eq2]
      nlinarith
    have h8 : (p - 29 / 18) * (p + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case p = 29/18
      right
      linarith
    · -- Case p = -1
      left
      linarith
    <;> nlinarith
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  <;> tauto
  all_goals norm_num
  <;> try { omega }
  all_goals nlinarith
  all_goals norm_num
  <;> try { nlinarith }
  all_goals nlinarith
  <;> try { tauto }
  <;> try { nlinarith <;> nlinarith }
  all_goals nlinarith
  all_goals try { tauto <;> tauto }
  all_goals nlinarith