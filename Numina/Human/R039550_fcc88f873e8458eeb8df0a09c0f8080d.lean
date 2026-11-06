import Mathlib

open Real Set
open scoped BigOperators

/-
If the function $f(x)=\sqrt{k x^{2}+k x+3}$ has the domain $\mathbf{R}$, then the range of values for $k$ is
-/
theorem algebra_185414 (k : ℝ) :
  (∀ x : ℝ, ∃ y : ℝ, y^2 = k * x^2 + k * x + 3) ↔ 0 ≤ k ∧ k ≤ 12 := by
  constructor
  · -- Assume that for all x, there exists y such that y^2 = k*x^2 + k*x + 3, prove 0 ≤ k and k ≤ 12
    intro h
    have h1 := h (-1 / 2)
    rcases h1 with ⟨y1, hy1⟩
    have h2 : k ≤ 12 := by
      have h1 : 3 - k / 4 ≥ 0 := by
        nlinarith [sq_nonneg y1, hy1]
      linarith
    have h3 : 0 ≤ k := by
      by_contra hk
      push_neg at hk
      have h4 := h (-3 / k)
      rcases h4 with ⟨y4, hy4⟩
      have h5 : k ≠ 0 := by linarith
      have h6 : 9 / k ≥ 0 := by
        have h7 : k * (-3 / k) ^ 2 + k * (-3 / k) + 3 = 9 / k := by
          field_simp [h5]
          ring
        rw [h7] at hy4
        nlinarith [sq_nonneg y4]
      have h8 : 9 / k < 0 := by
        apply div_neg_of_pos_of_neg
        · norm_num
        · linarith
      linarith
    exact ⟨h3, h2⟩
  · -- Assume 0 ≤ k ≤ 12, prove that for all x, there exists y such that y^2 = k*x^2 + k*x + 3
    rintro ⟨hk1, hk2⟩
    intro x
    use Real.sqrt (k * x^2 + k * x + 3)
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg (x + 1 / 2), hk1, hk2]
