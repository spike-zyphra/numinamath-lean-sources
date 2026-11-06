import Mathlib

theorem number_theory_281450 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x * y * z ≠ 0 ∧ x^2 + y^5 = z^3} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 ^ (15 * t + 10), 2 ^ (6 * t + 4), 2 ^ (10 * t + 7)))
  · -- Show that the function f is injective.
    intro t s h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that every element in the image of f is in the set.
    intro t 
    refine ⟨?_, ?_⟩
    · -- Show that x * y * z ≠ 0
      simp
    · -- Show that x^2 + y^5 = z^3
      have h1 : (2 ^ (15 * t + 10) : ℤ) ^ 2 = 2 ^ (30 * t + 20) := by
        ring_nf
      have h2 : (2 ^ (6 * t + 4) : ℤ) ^ 5 = 2 ^ (30 * t + 20) := by
        ring_nf
      have h3 : (2 ^ (10 * t + 7) : ℤ) ^ 3 = 2 ^ (30 * t + 21) := by
        ring_nf
      rw [h1, h2, h3]
      ring_nf