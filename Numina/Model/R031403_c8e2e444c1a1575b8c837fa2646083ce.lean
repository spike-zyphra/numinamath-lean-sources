import Mathlib

theorem algebra_320943 {p q : ℝ} (h : ∃ α β, α ≠ β ∧ α^2 - 2 * α + Real.sqrt 3 / 2 = 0 ∧ β^2 - 2 * β + Real.sqrt 3 / 2 = 0 ∧
    α^4 + p * α^2 + q = 0 ∧ β^4 + p * β^2 + q = 0) :
    p = Real.sqrt 3 - 4 := by

  rcases h with ⟨α, β, hne, h1, h2, h3, h4⟩

  have eq1 : (α^2 - β^2) * (α^2 + β^2 + p) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h'
      apply hne
      linarith
    ), sq_nonneg (α^2 - β^2), sq_nonneg (α + β), sq_nonneg (α - β)]

  cases' (mul_eq_zero.mp eq1) with h5 h6

  · -- case h5 : α^2 - β^2 = 0
    have h5' : α^2 = β^2 := by linarith
    have h6' : α = -β := by
      have hne' : α ≠ β := hne
      have h7' : α^2 = β^2 := h5'
      have : α = β ∨ α = -β := by
        rw [sq_eq_sq_iff_eq_or_eq_neg] at h7'
        tauto
      cases this with
      | inl h8 => 
        exfalso
        apply hne'
        linarith
      | inr h9 =>
        tauto

    rw [show α = -β by exact h6'] at h1 h3
    have h7' : β = 0 := by
      nlinarith [Real.sqrt_nonneg 3]

    have h8' : α = 0 := by
      linarith [h6', h7']

    have h9' : α = β := by
      linarith [h8', h7']

    contradiction

  · -- case h6 : α^2 + β^2 + p = 0
    have eq2 : p = - (α^2 + β^2) := by
      nlinarith

    have eq3 : α^2 + β^2 = 2 * (α + β) - Real.sqrt 3 := by
      nlinarith [h1, h2]

    have eq4 : p = Real.sqrt 3 - 2 * (α + β) := by
      nlinarith [eq2, eq3]

    have eq5 : α + β = 2 := by 
      have eq6 : (β - α) * (α + β - 2) = 0 := by
        nlinarith [h1, h2, sq_pos_of_ne_zero (show (α - β : ℝ) ≠ 0 by
          intro h'
          apply hne
          linarith
        ), Real.sqrt_nonneg 3]

      cases' (mul_eq_zero.mp eq6) with eq7 eq8

      · -- case eq7 : β - α = 0
        exfalso
        apply hne
        linarith

      · -- case eq8 : α + β - 2 = 0
        linarith

    rw [eq4]
    nlinarith [eq5, Real.sqrt_nonneg 3]