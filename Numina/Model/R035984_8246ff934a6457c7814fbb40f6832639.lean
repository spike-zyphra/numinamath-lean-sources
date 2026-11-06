import Mathlib

theorem algebra_326532 {f : ℝ → ℝ} (h : ∀ x y, f (x + y ^ 2) = f x + 2 * f y ^ 2) (h' : f 1 ≠ 0) :
    f 2007 = 1003.5 := by
  have h1 : f 0 = 0 := by
    specialize h 0 0
    norm_num at h
    nlinarith
  have h1' : f 1 = 1 / 2 := by
    specialize h 0 1
    norm_num [h1] at h
    have h2 : f 1 * (2 * f 1 - 1) = 0 := by nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- `f 1 = 0` contradicts `f 1 ≠ 0`.
      exfalso
      exact h' h3
    · -- `f 1 = 1/2`.
      linarith
  have h2 : ∀ (x : ℝ), f (x + 1) = f x + 1 / 2 := by
    intro x
    specialize h x 1
    norm_num [h1'] at h
    linarith
  have h3 : ∀ (n : ℕ), f ((↑n : ℝ) + 1) = (↑n + 1 : ℝ) / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num [h1']
    | succ n ih =>
      have eq1 : f ((↑(n + 1 : ℕ) : ℝ) + 1) = f ((↑n : ℝ) + 1 + 1) := by
        simp
        <;> ring_nf
      rw [eq1]
      rw [show f ((↑n : ℝ) + 1 + 1) = f ((↑n : ℝ) + 1) + 1 / 2 by
        rw [show (↑n : ℝ) + 1 + 1 = (↑n + 1 : ℝ) + (1: ℝ) by ring]
        apply h2
      ]
      rw [ih]
      field_simp at *
      <;> ring_nf
  have eq2 : f (2007: ℝ) = (2007: ℝ)/2 := by
    have eq2 := h3 2006
    norm_num at eq2 ⊢
    linarith [eq2]
  rw [eq2]
  all_goals norm_num