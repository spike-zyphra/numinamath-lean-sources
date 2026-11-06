import Mathlib

theorem algebra_93274 (K : ℝ) :
    (∃ x : ℝ, x = K ^ 2 * (x - 1) * (x - 2)) ↔ K ∈ Set.univ := by
  constructor
  · -- (→) direction: if exists real root, then K is in univ
    intro h
    simp at h ⊢
    all_goals try tauto
  · -- (←) direction: K is in univ, need to show exists real root
    intro h
    simp at h ⊢
    by_cases h2 : K = 0
    · -- case K=0, the equation is x=0, so exists.
      use 0
      norm_num [h2]
    · -- K≠0, need to solve the quadratic
      have h2' : K ≠ 0 := by
        intro h'
        apply h2
        linarith
      use ( (3 * K ^ 2 + 1) + Real.sqrt (K^4 + 6 * K^2 + 1) ) / (2 * K^2)
      field_simp [h2']
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith [ Real.sqrt_nonneg (K^4 + 6 * K^2 + 1), Real.sq_sqrt (show 0 ≤ K^4 + 6 * K^2 + 1 by nlinarith) ]