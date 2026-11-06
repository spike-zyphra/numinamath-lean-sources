import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_186837 {f g : ℝ → ℝ}
  (hf : f = λ x => exp (2 * x) - 1) (hg : g = λ x => log (x + 1)) :
  {x | f (g x) - g (f x) ≤ 1 ∧ x+1>0 ∧ (f x)+1>0} = {x | -1 < x ∧ x ≤ 1} := by
  ext x
  simp only [hf, hg, Set.mem_setOf_eq]
  constructor
  · -- Assume h: f (g x) - g (f x) ≤ 1 ∧ x+1>0 ∧ (f x)+1>0, prove h': -1 < x ∧ x ≤ 1
    rintro ⟨h1, hx1, hfx1⟩
    have h2 : exp (2 * (log (x + 1))) = (x + 1) ^ 2 := by
      have h3 : 2 * (log (x + 1)) = log ((x + 1) ^ 2) := by
        simp [log_pow]
      rw [h3]
      rw [exp_log]
      all_goals nlinarith
    have h3 : log (exp (2 * x) - 1 + 1) = 2 * x := by
      have h4 : exp (2 * x) - 1 + 1 = exp (2 * x) := by
        ring_nf
      rw [h4]
      rw [log_exp]
    have h4 : (exp (2 * (log (x + 1))) - 1) - (2 * x) ≤ 1 := by
      simp [h3] at h1 ⊢
      linarith
    have h5 : x ^ 2 ≤ 1 := by
      have h6 : (exp (2 * (log (x + 1)))) = (x + 1) ^ 2 := h2
      nlinarith [sq_nonneg (x + 1), Real.exp_nonneg (2 * (log (x + 1)))]
    constructor
    · -- Show that -1 < x
      linarith
    · -- Show that x ≤ 1
      nlinarith [h5]
  · -- Assume h: -1 < x ∧ x ≤ 1, prove h': f (g x) - g (f x) ≤ 1 ∧ x+1>0 ∧ (f x)+1>0
    rintro ⟨hx1, hx2⟩
    have h2 : exp (2 * (log (x + 1))) = (x + 1) ^ 2 := by
      have h3 : 2 * (log (x + 1)) = log ((x + 1) ^ 2) := by
        simp [log_pow]
      rw [h3]
      rw [exp_log]
      all_goals nlinarith
    have h3 : log (exp (2 * x) - 1 + 1) = 2 * x := by
      have h4 : exp (2 * x) - 1 + 1 = exp (2 * x) := by
        ring_nf
      rw [h4]
      rw [log_exp]
    have h4 : (exp (2 * (log (x + 1))) - 1) - (2 * x) ≤ 1 := by
      have h6 : (exp (2 * (log (x + 1)))) = (x + 1) ^ 2 := h2
      nlinarith [sq_nonneg (x), sq_nonneg (x - 1), Real.exp_nonneg (2 * (log (x + 1)))]
    constructor
    · -- Show that f (g x) - g (f x) ≤ 1
      simp [h3] at *
      linarith
    constructor
    · -- Show that x + 1 > 0
      linarith
    · -- Show that (f x) + 1 > 0
      have hx3 : exp (2 * x) > 0 := by positivity
      simp at *
      all_goals linarith [Real.exp_pos (2 * x)]