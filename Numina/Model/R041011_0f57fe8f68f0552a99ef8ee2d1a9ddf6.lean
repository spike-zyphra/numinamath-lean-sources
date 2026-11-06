import Mathlib

theorem algebra_290037 :
  {(a, d) : ℤ × ℤ | ∀ (n : ℕ), ∑ i in Finset.range n, (a + d * i) = 4 * n ^ 2} =
  {(4, 8)} := by
  ext ⟨a, d⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (a, d) is in the set
    intro h
    have h1 := h 0
    simp [Finset.sum_range_zero] at h1
    have h2 := h 1
    simp [Finset.sum_range_succ] at h2
    have h3 := h 2
    simp [Finset.sum_range_succ] at h3
    have h4 : (a : ℤ) = 4 := by
      omega
    have h5 : (d : ℤ) = 8 := by
      omega
    simp [h4, h5]
  · -- Assume (a, d) = (4, 8), prove that sum of first n terms is 4n^2
    rintro ⟨rfl, rfl⟩
    intro n
    have h : ∀ (n : ℕ), ∑ i in Finset.range n, (4 + (8 : ℤ) * i) = 4 * (n : ℤ) ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring_nf <;> omega
    specialize h n
    simpa using h