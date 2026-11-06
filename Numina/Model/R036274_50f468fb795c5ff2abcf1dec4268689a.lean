import Mathlib

theorem algebra_9459 {f : ℝ → ℝ} (hf : Function.Periodic f 2)
    (h : ∀ x ∈ Set.Ico 0 2, f x = x ^ 3 - x) :
    ∀ x ∈ Set.Ico (-2) 0, f x = x ^ 3 + 6 * x ^ 2 + 11 * x + 6 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : f x = f (x + 2) := by 
    rw [hf x]
  have hx3 : 0 ≤ x + 2 := by linarith 
  have hx4 : x + 2 < 2 := by linarith 
  have h2 : f (x + 2) = (x + 2) ^ 3 - (x + 2) := by 
    apply h 
    constructor
    · linarith 
    · linarith 
  rw [h1, h2]
  ring