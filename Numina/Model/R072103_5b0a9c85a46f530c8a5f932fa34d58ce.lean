import Mathlib

theorem algebra_136672 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + 1) :
    ∀ x, f (f (x) + x) / f (x) = x ^ 2 + 2 * x + 2 := by
  intro x
  have h1 : f x = x ^ 2 + 1 := hf x
  have h2 : f (x) + x = x ^ 2 + 1 + x := by
    rw [hf x]
  have h3 : f (f (x) + x) = (x ^ 2 + 1 + x) ^ 2 + 1 := by
    rw [h2]
    apply hf
  rw [h3, h1]
  field_simp
  <;> ring