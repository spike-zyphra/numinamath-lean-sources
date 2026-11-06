import Mathlib

theorem algebra_181849 (a d : ℚ) (h₀ : 0 < a) (h₁ : 0 < d)
    (h₂ : (a + d) * (a + 4 * d) = (a + 8 * d) ^ 2) :
    IsLeast {k | 0 < k ∧ ∑ i ∈ Finset.range k, (a + i * d) > 100 * a} 34 := by

  have h₃ : a = 8 * d := by
    nlinarith [h₂, mul_pos h₀ h₁, sq_pos_of_pos h₀, sq_pos_of_pos h₁]

  constructor
  · -- Show 34 is in the set
    constructor
    · -- Show 34 > 0
      norm_num
    · -- Show sum from k=34 is greater than 100*a
      rw [h₃]
      norm_num [Finset.sum_range_succ]
      <;> nlinarith [h₀, h₁]
  · -- Show that 34 is minimal
    intro k hk
    rcases hk with ⟨hk_pos, hk_sum⟩
    by_contra h
    push_neg at h
    have h4 : k ≤ 33 := by linarith
    have h₄ : ∑ i in Finset.range k, (a + i * d) ≤ 100 * a := by
      have h₅ : a = 8 * d := h₃
      rw [h₅]
      have h6 : ∀ (k : ℕ), ∑ i in Finset.range k, (8 * d + (i : ℚ) * d) ≤ 100 * (8 * d) := by
        intro k
        induction k with
        | zero =>
          norm_num
          <;> nlinarith
        | succ k ih =>
          simp [Finset.sum_range_succ] at ih ⊢
          <;> nlinarith [sq_nonneg (d), sq_nonneg ((k : ℚ) * d - 33 * d), sq_nonneg ((k : ℚ) * d), sq_nonneg (k * d - 33 * d), mul_pos h₁ (show 0 < (8 : ℚ) by norm_num)]
      apply h6 k
    linarith [hk_sum, h₄]
    <;> try { linarith [sq_nonneg (d), sq_nonneg ((k : ℚ) * d - 33 * d), sq_nonneg ((k : ℚ) * d), sq_nonneg (k * d - 33 * d)] }
    <;> try { linarith }
    <;> try { nlinarith }