import Mathlib.Tactic

theorem algebra_122975 (α : ℝ) :
    (∀ a b c : ℝ, (∀ x ∈ Set.Icc 0 1, |a * x ^ 2 + b * x + c| ≤ 1) → |(2 * a) * 0 + b| ≤ α) ↔
    α ≥ 8 := by
  constructor
  · -- First direction: If the implication holds for all a,b,c, then α ≥ 8
    intro h
    have h1 := h 8 (-8) 1 (by
      intro x hx
      have h0 : 0 ≤ x := by
        have h0 : x ≥ 0 := by
          have h0 : x ∈ Set.Icc 0 1 := hx
          exact h0.1
        linarith
      have h1 : x ≤ 1 := by
        have h1 : x ∈ Set.Icc 0 1 := hx
        exact h1.2
      have h2 : -1 ≤ 8 * x ^ 2 + (-8) * x + 1 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (x - 1)]
      have h3 : 8 * x ^ 2 + (-8) * x + 1 ≤ 1 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (x - 1)]
      apply abs_le.mpr
      constructor <;> nlinarith
    )
    norm_num at h1 ⊢
    all_goals linarith
  · -- Now prove the converse. If α ≥ 8, then for all a,b,c, if |p(x)| ≤ 1 on [0,1], then |p'(0)| ≤ α
    intro h a b c h1
    have h2 := h1 0 (by norm_num)
    have h3 := h1 1 (by norm_num)
    have h4 := h1 (1 / 2) (by norm_num)
    have h2 := abs_le.mp h2
    have h3 := abs_le.mp h3
    have h4 := abs_le.mp h4
    have h11 : |(2 * a) * 0 + b| = |b| := by
      simp
    rw [h11]
    have h12 : |b| ≤ 8 := by
      apply abs_le.mpr
      constructor <;> nlinarith
    linarith