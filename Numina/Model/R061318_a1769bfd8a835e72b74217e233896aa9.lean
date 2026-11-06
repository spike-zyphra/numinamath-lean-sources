import Mathlib

theorem algebra_324573 {f : ℝ → ℝ} (C : ℝ → ℝ) (hC : C = fun x => f x)
    (C1 : ℝ → ℝ) (hC1 : C1 = fun x => f (2 - x)) (C2 : ℝ → ℝ)
    (hC2 : C2 = fun x => C1 (x + 1)) :
    ∀ x, C2 x = f (1 - x) := by 
  intro x
  calc 
    C2 x = C1 (x + 1) := by rw [hC2]
    _ = f (2 - (x + 1)) := by rw [hC1]
    _ = f (1 - x) := by ring_nf