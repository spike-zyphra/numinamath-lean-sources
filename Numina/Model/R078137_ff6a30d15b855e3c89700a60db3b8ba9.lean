import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314290 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  (f : ℝ → ℝ) (hf : f = λ x => a^2 / x + b^2 / (1 - x)) :
  IsLeast {y | ∃ x, 0 < x ∧ x < 1 ∧ y = f x} ((a + b)^2) := by

  constructor
  · -- Prove (a + b)^2 is achievable
    use a / (a + b)
    constructor
    · -- Show that 0 < a / (a + b)
      have h1 : 0 < a / (a + b) := by
        apply div_pos
        all_goals linarith
      exact h1
    constructor
    · -- Show that a / (a + b) < 1
      have h2 : a / (a + b) < 1 := by
        have h1 : a + b > 0 := by linarith
        have h3 : a < a + b := by linarith
        apply (div_lt_iff (by linarith)).mpr
        linarith
      exact h2
    · -- Show that (a + b)^2 = f (a / (a + b))
      rw [hf]
      field_simp [(show a + b ≠ 0 by linarith), (show a > 0 by linarith), (show b > 0 by linarith)]
      <;> ring
  · -- Prove (a + b)^2 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx1, hx2, hy_eq⟩
    rw [hy_eq]
    have h1 : 0 < x := hx1
    have h2 : x < 1 := hx2
    rw [hf]
    have h3 : a^2 / x + b^2 / (1 - x) ≥ (a + b) ^ 2 := by
      have h4 : 0 < x := hx1
      have h5 : 0 < 1 - x := by linarith
      have h6 : a^2 / x + b^2 / (1 - x) - (a + b) ^ 2 ≥ 0 := by
        have h7 : a^2 / x + b^2 / (1 - x) - (a + b) ^ 2 =
          (a^2 * (1 - x) + b^2 * x - (a + b) ^ 2 * x * (1 - x)) / (x * (1 - x)) := by
          field_simp [hx1, show 1 - x ≠ 0 by linarith]
          ring
        have h8 : a^2 * (1 - x) + b^2 * x - (a + b) ^ 2 * x * (1 - x) ≥ 0 := by
          nlinarith [sq_nonneg (a * (1 - x) - b * x), sq_nonneg (a * x - b * (1 - x)), sq_nonneg (a - b), sq_nonneg (x - (a / (a + b)))]
        have h9 : 0 < x * (1 - x) := by
          nlinarith
        have h10 : (a^2 * (1 - x) + b^2 * x - (a + b) ^ 2 * x * (1 - x)) / (x * (1 - x)) ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals nlinarith
        linarith [h7, h10]
      linarith [h6]
    linarith [h3]