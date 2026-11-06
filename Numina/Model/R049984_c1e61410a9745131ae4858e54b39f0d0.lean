import Mathlib

theorem algebra_98104 (m n p q : ℝ) (f g : ℝ → ℝ) (hf : f = fun x => m * x + n) (hg : g = fun x => p * x + q) : (∃ x, f (g x) = g (f x)) ↔ n * (1 - p) - q * (1 - m) = 0 := by
  constructor
  · -- Assume there exists x such that f(g(x)) = g(f(x)), prove n(1-p) - q(1-m) = 0
    rintro ⟨x, hx⟩
    rw [hf, hg] at hx
    simp at hx
    linarith
  · -- Assume n(1-p) - q(1-m) = 0, prove there exists x such that f(g(x)) = g(f(x))
    intro h
    use 0
    rw [hf, hg]
    simp at h ⊢
    linarith