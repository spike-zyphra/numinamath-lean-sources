import Mathlib

theorem algebra_606074 {f : ℝ → ℝ} : (∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f (1 - 1 / x) = 1 + x) ↔ ∀ x, x ≠ 0 ∧ x ≠ 1 → f x = (-x ^ 3 + x ^ 2 + 1) / (2 * x * (1 - x)) := by
  constructor
  · -- Assume the functional equation holds, prove the formula for f(x).
    intro h
    intro x hx
    have h1 : x ≠ 0 := hx.1
    have h2 : x ≠ 1 := hx.2
    have eq1 := h x ⟨h1, h2⟩
    have h3 : 1 - 1 / x ≠ 0 := by
      by_contra h3
      have h4 : 1 / x = 1 := by linarith
      have h5 : x = 1 := by
        field_simp [h1] at h4 ⊢
        all_goals linarith
      tauto
    have h4 : 1 - 1 / x ≠ 1 := by
      by_contra h4
      have h5 : 1 / x = 0 := by linarith
      have h6 : x ≠ 0 := h1
      field_simp at h5
    have eq2 := h (1 - 1 / x) ⟨h3, h4⟩
    have h7 : 1 / (1 - x) ≠ 0 := by
      by_contra h7
      have h8 : 1 - x = 0 := by
        have : 1 / (1 - x) = 0 := by linarith
        have : 1 - x = 0 := by
          by_contra h
          have : 1 / (1 - x) ≠ 0 := by
            field_simp [h]
          tauto
        linarith
      have h9 : x = 1 := by linarith
      tauto
    have h8 : 1 / (1 - x) ≠ 1 := by
      by_contra h8
      have h9 : 1 - x = 1 := by
        field_simp [(show 1 - x ≠ 0 by
          by_contra h
          have : x = 1 := by linarith
          tauto
        )] at h8 ⊢
        all_goals linarith
      have h10 : x = 0 := by linarith
      tauto
    have eq3 := h (1 / (1 - x)) ⟨h7, h8⟩
    have eq1' : 1 - 1 / (1 - 1 / x) = (1 / (1 - x) ) := by 
      field_simp [(show x ≠ 0 by exact h1), (show x - 1 ≠ 0 by
        by_contra h
        have : x = 1 := by linarith
        tauto
      ), (show 1 - x ≠ 0 by
        by_contra h
        have : x = 1 := by linarith
        tauto
      )]
    rw [eq1'] at eq2
    have eq2' : 1 - 1 / (1 / (1 - x)) = x := by
      field_simp [(show 1 - x ≠ 0 by
        by_contra h
        have : x = 1 := by linarith
        tauto
      ), (show x ≠ 0 by exact h1)]
    rw [eq2'] at eq3
    have eq4 : f x = (x + 1 / x + 1 / (1 - x)) / 2 := by
      linarith
    have eq5 : f x = (-x^3 + x^2 + 1) / (2 * x * (1 - x)) := by
      rw [eq4]
      field_simp [(show x ≠ 0 by exact h1), (show 1 - x ≠ 0 by
        by_contra h
        have : x = 1 := by linarith
        tauto
      )]
      ring
    exact eq5
  · -- Assume the formula for f(x), prove the functional equation.
    intro h x hx
    have h1 : x ≠ 0 := hx.1
    have h2 : x ≠ 1 := hx.2
    have eq1 : f x = (-x^3 + x^2 + 1) / (2 * x * (1 - x)) := by
      apply h x
      exact ⟨h1, h2⟩
    have h3 : 1 - 1 / x ≠ 0 := by
      by_contra h3
      have h4 : 1 / x = 1 := by linarith
      have h5 : x = 1 := by
        field_simp [h1] at h4 ⊢
        all_goals linarith
      tauto
    have h4 : 1 - 1 / x ≠ 1 := by
      by_contra h4
      have h5 : 1 / x = 0 := by linarith
      have h6 : x ≠ 0 := h1
      field_simp at h5
    have eq2 : f (1 - 1 / x) = (-(1 - 1 / x)^3 + (1 - 1 / x)^2 + 1) / (2 * (1 - 1 / x) * (1 - (1 - 1 / x)) ) := by
      apply h (1 - 1 / x) 
      constructor
      · -- Show 1 - 1 / x ≠ 0
        exact h3
      · -- Show 1 - 1 / x ≠ 1
        exact h4
    rw [eq1, eq2]
    field_simp [(show x ≠ 0 by exact h1), (show x - 1 ≠ 0 by
      by_contra h
      have : x = 1 := by linarith
      tauto
    ), (show 1 - x ≠ 0 by
      by_contra h
      have : x = 1 := by linarith
      tauto
    )]
    ring