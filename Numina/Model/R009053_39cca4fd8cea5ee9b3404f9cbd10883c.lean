import Mathlib

theorem algebra_180008 (m n p q : ℝ) (f g : ℝ → ℝ)
    (hf : f = fun x => m * x + n) (hg : g = fun x => p * x + q) :
    (∃ x, f (g x) = g (f x)) ↔ n * (1 - p) - q * (1 - m) = 0 := by
  constructor
  · -- Assume there's a solution x, prove n * (1-p) - q * (1-m) = 0
    rintro ⟨x, hx⟩
    simp [hf, hg] at hx
    linarith
  · -- Assume n * (1-p) - q * (1-m) = 0, prove there's a solution
    intro h
    use 0
    simp [hf, hg]
    linarith