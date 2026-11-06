import Mathlib

theorem algebra_6902 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 6 * x - 16) :
    IsLeast (Set.range f) (-25) := by 
  have h1 : ∀ x, f x = (x + 3) ^ 2 - 25 := by 
    intro x 
    rw [hf]
    ring 
  have h2 : -25 ∈ Set.range f := by 
    use -3 
    rw [h1] 
    norm_num 
  have h3 : ∀ y ∈ Set.range f, -25 ≤ y := by 
    intro y hy 
    obtain ⟨x, hx⟩ := hy 
    rw [h1 x] at hx 
    have h4 : (x + 3) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    linarith 
  exact ⟨h2, h3⟩