import Mathlib

theorem algebra_321691 (f : ℤ → ℤ) (hf : ∀ x, |x| ≤ 2 → f x = 2 * x + 3) :
    f '' {x | |x| ≤ 2} = {-1, 1, 3, 5, 7} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, we prove that if y ∈ f''{x | |x| ≤ 2}, then y ∈ {-1, 1, 3, 5, 7}
    rintro ⟨x, hx, rfl⟩
    have hfx : f x = 2 * x + 3 := hf x hx
    rw [hfx]
    have h : x ≥ -2 ∧ x ≤ 2 := by 
      have h1 : |x| ≤ 2 := hx
      cases' abs_le.mp h1 with h2 h3
      constructor
      · linarith
      · linarith
    have h1 : x ≥ -2 := h.1
    have h2 : x ≤ 2 := h.2
    interval_cases x <;> tauto
  · -- Now the reverse direction: if y ∈ {-1, 1, 3, 5, 7}, then y ∈ f''{x | |x| ≤ 2}
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- y = -1
      use -2
      all_goals norm_num [hf]
    · -- y = 1
      use -1
      all_goals norm_num [hf]
    · -- y = 3
      use 0
      all_goals norm_num [hf]
    · -- y = 5
      use 1
      all_goals norm_num [hf]
    · -- y = 7
      use 2
      all_goals norm_num [hf]