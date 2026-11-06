import Mathlib

theorem inequalities_228619 (A B p q : ℝ) (h₀ : 0 < A) (h₁ : 0 < B)
    (h₂ : 0 < p) (h₃ : 0 < q) (h₄ : 1 / p + 1 / q = 1) :
    A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) ≤ A / p + B / q := by

  have h8 : (1 : ℝ) / p ≥ 0 := by positivity
  have h9 : (1 : ℝ) / q ≥ 0 := by positivity
  have h10 : (1 : ℝ) / p + (1 : ℝ) / q = 1 := h₄
  have h11 : A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) ≤ (1 / p) * (A) + (1 / q) * (B) := by 
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try positivity
      try linarith
  have h12 : (1 / p) * (A) + (1 / q) * (B) = A / p + B / q := by 
    field_simp
    <;> ring
  rw [h12] at h11
  linarith