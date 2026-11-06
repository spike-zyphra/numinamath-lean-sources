import Mathlib

theorem algebra_13043 :
    IsGreatest {x : ℕ | 0 < x ∧ (x ^ 4 / x ^ 2 : ℝ) < 10} 3 := by
  constructor
  · -- Show 3 is in the set
    constructor
    · norm_num
    · -- Verify $\frac{3^4}{3^2} < 10$
      norm_num
  · -- Show that if x is in the set, then x ≤ 3
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    by_contra h
    push_neg at h
    have h1 : x ≥ 4 := by linarith
    have h2 : (x : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h1
    have h4 : (x ^ 4 : ℝ) / (x ^ 2 : ℝ) = (x ^ 2 : ℝ) := by
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring
    have h5 : (x ^ 2 : ℝ) ≥ (16 : ℝ) := by
      have h6 : (x : ℝ) ≥ (4 : ℝ) := h2
      nlinarith [sq_nonneg ((x : ℝ) - (4 : ℝ)), sq_nonneg ((x : ℝ))]
    have h6 : (x ^ 4 : ℝ) / (x ^ 2 : ℝ) ≥ (16 : ℝ) := by
      linarith [h4, h5]
    linarith [h6, hx1]
    all_goals try { tauto }
    <;> norm_num
    all_goals try { tauto }
    <;> norm_num