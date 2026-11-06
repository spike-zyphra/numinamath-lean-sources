import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_148955 (f g : ℝ → ℝ)
  (hf : f = λ x => abs x) (hg : g = λ x => sqrt (x^2 - 2 * abs x + 1)) :
  ∀ x, |f x - 1| = g x := by
  intro x
  have hfx : f x = abs x := by simp [hf]
  have hgx : g x = sqrt (x^2 - 2 * abs x + 1) := by simp [hg]
  rw [hfx, hgx]
  have h1 : x^2 - 2 * abs x + 1 = (abs x - 1)^2 := by
    cases le_or_lt 0 x with
    | inl h2 =>
      -- x ≥ 0, so |x| = x
      rw [abs_of_nonneg h2]
      ring
    | inr h2 =>
      -- x < 0, so |x| = -x
      rw [abs_of_neg h2]
      ring
  rw [h1]
  rw [Real.sqrt_sq_eq_abs]
  <;> ring_nf <;> simp [abs_sub]
  <;> ring