import Mathlib

open Real

theorem inequalities_312968 (p q : ℝ → Prop)
    (hp : p = fun x => (x ^ 2 + x + 1) * sqrt (x + 3) ≥ 0)
    (hq : q = fun x => x ≥ -2) :
    ¬(∀ x, p x → q x) ∧ (∀ x, q x → p x) := by
  have h1 : ¬(∀ x, p x → q x) := by
    intro h
    have h2 := h (-3)
    rw [hp] at h2
    rw [hq] at h2
    norm_num [Real.sqrt_eq_zero] at h2
    all_goals norm_num at h2
  have h2 : ∀ x, q x → p x := by
    intro x hx
    rw [hp]
    rw [hq] at hx
    have h3 : x ≥ -2 := hx
    have h4 : x + 3 ≥ 1 := by linarith
    have h5 : sqrt (x + 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h6 : x ^ 2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h7 : (x ^ 2 + x + 1) * sqrt (x + 3) ≥ 0 := by
      have h8 : sqrt (x + 3) ≥ 0 := h5
      have h9 : x ^ 2 + x + 1 > 0 := h6
      nlinarith [h8, h9]
    linarith
  exact ⟨h1, h2⟩