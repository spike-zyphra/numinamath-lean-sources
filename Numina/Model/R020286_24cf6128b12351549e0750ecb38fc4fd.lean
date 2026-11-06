import Mathlib

theorem algebra_21110 : {x : ℕ | 0 < x ∧ x < 200 * Real.pi}.encard = 628 := by
  have h1 : (200 * Real.pi : ℝ) > 628 := by 
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h2 : (200 * Real.pi : ℝ) < 629 := by 
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h3 : {x : ℕ | 0 < x ∧ x < 200 * Real.pi} = Set.Icc 1 628 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume $0 < n < 200 * \pi$
      intro h 
      rcases h with ⟨h0, h1⟩
      have h1' : (n : ℝ) < (629 : ℝ) := by
        have h11 : (n : ℝ) < (200 * Real.pi : ℝ) := by exact_mod_cast h1
        have h12 : (200 * Real.pi : ℝ) < (629 : ℝ) := h2
        linarith 
      have h2 : n ≤ 628 := by
        by_contra h
        push_neg at h 
        have h3 : n ≥ 629 := by omega 
        have h4 : (n : ℝ) ≥ (629 : ℝ) := by exact_mod_cast h3 
        linarith 
      constructor 
      · -- Show $1 \leq n$: 
        omega 
      · -- Show $n \leq 628$:
        omega 
    · -- Assume $1 \leq n \leq 628$
      rintro ⟨hn1, h2⟩
      constructor 
      · -- Show $n > 0$:
        omega 
      · -- Show $n < 200 * \pi$:
        have h3 : (n : ℝ) ≤ (628 : ℝ) := by
          exact_mod_cast h2 
        have h11 : (200 * Real.pi : ℝ) > (628 : ℝ) := h1 
        have h4 : (n : ℝ) < (200 * Real.pi : ℝ) := by 
          linarith
        exact_mod_cast h4
  rw [h3]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> norm_num