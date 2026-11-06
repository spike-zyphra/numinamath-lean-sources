import Mathlib

theorem algebra_145898 {K E F G : Type*} [Field K] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module K E] [Module K F] [Module K G] (f : E →ₗ[K] F) (g : F →ₗ[K] G) :
    g ∘ f = 0 ↔ f '' Set.univ ⊆ g ⁻¹' {0} := by
  constructor
  · -- Forward direction: if g ∘ f = 0 then f '' Set.univ ⊆ g⁻¹' {0}
    intro h 
    have h1 : ∀ x : E, g (f x) = 0 := by
      intro x 
      simpa using congr_fun h x 
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    have h2 : g y = 0 := by 
      have h_eq : f x = y := by 
        tauto 
      have h1' : g (f x) = 0 := h1 x 
      rw [h_eq] at * 
      all_goals 
        try { exact h1' }
    show y ∈ g ⁻¹' {0} 
    simp [h2] 
  · -- Backward direction: if f '' Set.univ ⊆ g⁻¹' {0} then g ∘ f = 0 
    intro h 
    funext x 
    have h1 : f x ∈ f '' Set.univ := by 
      use x 
      all_goals 
        simp 
    have h2 : f x ∈ g ⁻¹' {0} := h h1 
    simp at h2 ⊢ 
    exact h2