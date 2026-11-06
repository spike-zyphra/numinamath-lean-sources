import Mathlib

theorem number_theory_286536 :
    {n : ℤ | (37 * n) % 31 = 15} = {31 * k - 13 | k : ℤ} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume (37 * n) % 31 = 15, prove ∃ k, n = 31 * k - 13
    intro h
    have h1 : (37 * n) % 31 = 15 := h
    have h2 : n % 31 = 18 := by 
      omega
    refine' ⟨(n / 31 + 1), by omega⟩
  · -- Assume ∃ k, n = 31 * k - 13, prove (37 * n) % 31 = 15
    rintro ⟨k, rfl⟩
    omega