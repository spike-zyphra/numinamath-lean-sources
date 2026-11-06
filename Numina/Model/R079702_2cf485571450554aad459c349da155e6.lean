import Mathlib

theorem algebra_198677 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (x : ℕ → ℝ) (hx : ∃ d, ∀ n, x n = x 0 + d * n) :
    ∃ d, ∀ n, f (x n) = f (x 0) + d * n := by 
  rcases hf with ⟨a, b, hfab⟩
  rcases hx with ⟨d, had⟩
  use a * d
  intro n
  simp [hfab, had n]
  <;> ring_nf <;> simp [mul_add]
  <;> ring