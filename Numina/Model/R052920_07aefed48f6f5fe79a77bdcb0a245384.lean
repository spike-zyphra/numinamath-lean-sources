import Mathlib

theorem algebra_282683 {φ : ℝ → ℝ} (hφ : Function.LeftInverse (φ⁻¹) φ)
    (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -φ x) :
    f = fun x => -φ (-x) := by 
  funext x
  calc
    f x = f (- (-x)) := by simp -- x = -(-x)
    _   = -φ (-x)   := by rw [hf (-x)] -- apply the hypothesis hf to -x