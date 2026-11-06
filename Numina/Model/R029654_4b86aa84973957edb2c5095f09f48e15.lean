import Mathlib

theorem algebra_161484 {f : ℝ → ℝ} {T α : ℝ} (hT : T > 0) (hf : Function.Periodic f T)
    (hα : α > 0) :
    Function.Periodic (fun x => f (α * x)) (T / α) := by 
  unfold Function.Periodic
  intro x 
  calc
    (fun (y : ℝ) => f (α * y)) (x + T / α)
        = f (α * (x + T / α)) := by rfl
    _ = f (α * x + α * (T / α)) := by rw [mul_add]
    _ = f (α * x + T) := by 
      have h : α * (T / α) = T := by
        field_simp [ne_of_gt hα]
      rw [h]
    _ = f (α * x) := by 
      have h2 : f (α * x + T) = f (α * x) := by
        have h2 : f (α * x + T) = f (α * x) := by
          apply hf
        exact h2
      simpa using h2 
    _ = (fun (y : ℝ) => f (α * y)) x := by rfl