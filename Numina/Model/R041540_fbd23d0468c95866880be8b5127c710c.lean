import Mathlib

theorem algebra_13195 :
    {a | {x | 3 * (2 * x - a) = 2 * (3 * x + 12)}.Infinite} = {-8} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume {x | 3 * (2 * x - a) = 2 * (3 * x + 12)}.Infinite, prove a = -8
    intro h 
    by_contra h1
    push_neg at h1 
    have h6 : ∀ x : ℤ, ¬ (3 * (2 * x - a) = 2 * (3 * x + 12)) := by
      intro x 
      intro h_eq
      have eq1 : 3 * (2 * x - a) = 2 * (3 * x + 12) := h_eq 
      have eq2 : a = -8 := by 
        ring_nf at eq1 ⊢ 
        omega 
      contradiction 
    -- Now we have that the set is empty 
    have h7 : {x : ℤ | 3 * (2 * x - a) = 2 * (3 * x + 12)} = ∅ := by 
      ext x 
      simp [h6] 
    -- Contradiction because set is infinite
    rw [h7] at h 
    simp at h
  · -- Assume a = -8, prove {x | 3 * (2 * x - a) = 2 * (3 * x + 12)}.Infinite 
    intro h_eq 
    rw [h_eq] 
    have h5 : {x : ℤ | 3 * (2 * x - (-8 : ℤ)) = 2 * (3 * x + 12)} = Set.univ := by 
      ext x 
      simp 
      <;> ring
    rw [h5]
    simp [Set.infinite_univ]