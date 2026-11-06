import Mathlib

theorem inequalities_13471 :
    Set.ncard {x : ℕ | x > 0 ∧ x ^ 2 < 16 * x + 80} = 19 := by
  have h1 : {x : ℕ | x > 0 ∧ x ^ 2 < 16 * x + 80} = Finset.Icc 1 19 := by
    ext x
    simp
    constructor
    · -- Assume h : x > 0 ∧ x ^ 2 < 16 * x + 80, prove 1 ≤ x ∧ x ≤ 19
      intro h
      rcases h with ⟨hx1, h2⟩
      have h3 : x ≤ 19 := by
        nlinarith [sq_nonneg (x : ℕ), sq_nonneg ((x : ℕ) - 20)]
      have h4 : 1 ≤ x := by linarith
      omega
    · -- Assume 1 ≤ x ≤ 19, prove x > 0 ∧ x ^ 2 < 16 * x + 80
      intro h
      rcases h with ⟨h1, h2⟩
      have hx1 : x > 0 := by linarith
      have hineq : x ^ 2 < 16 * x + 80 := by
        interval_cases x <;> omega
      exact ⟨hx1, hineq⟩
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide