import Mathlib

theorem algebra_21499 {f : ℝ → ℝ} (x : ℝ) (hf : f = fun x => 5 * x - 12) (hx : f ⁻¹' {x} = {f (x + 1)}) : x = 47 / 24 := by
  have h1 : ∀ y, f y = x ↔ y = f (x + 1) := by
    apply Set.ext_iff.1 at hx
    intro y
    specialize hx y
    simp [hf] at hx ⊢
    simpa using hx
  have h2 : f (f (x + 1)) = x := by
    specialize h1 (f (x + 1))
    simpa using h1.2 rfl
  have h3 : f (x + 1) = 5 * (x + 1) - 12 := by 
    rw [hf]
  have h4 : f (f (x + 1)) = 5 * (5 * (x + 1) - 12) - 12 := by
    rw [show f (x + 1) = 5 * (x + 1) - 12 by exact h3]
    all_goals 
      simp [hf] 
  have h5 : f (f (x + 1)) = x := h2
  -- Substitute h4 into h5 to get an equation in x
  rw [h4] at h5 
  -- Now h5 is 5 * (5 * (x + 1) - 12) - 12 = x
  -- This simplifies to 24x = 47
  have eq1 : 5 * (5 * (x + 1) - 12) - 12 = 25 * x - 47 := by 
    ring 
  have eq2 : 25 * x - 47 = x := by 
    linarith [eq1, h5] 
  have eq3 : 24 * x = 47 := by 
    linarith [eq2]
  have hx2 : x = 47 / 24 := by
    linarith [eq3]
  exact hx2