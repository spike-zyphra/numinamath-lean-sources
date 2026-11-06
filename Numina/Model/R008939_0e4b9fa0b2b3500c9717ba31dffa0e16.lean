import Mathlib

theorem algebra_10394 {δ φ : ℝ → ℝ}  (x : ℝ)
    (hδ : δ = fun x => 3 * x + 8) (hφ : φ = fun x => 8 * x + 7)
    : {x |  δ (φ x) = 7} = {-11 / 12} := by 
  ext x
  simp [hδ, hφ]
  constructor
  · -- Forward direction: If δ(φ(x)) = 7, then x = -11/12
    intro h
    linarith
  · -- Backward direction: If x = -11/12, then δ(φ(x)) = 7
    intro h
    rw [h]
    norm_num