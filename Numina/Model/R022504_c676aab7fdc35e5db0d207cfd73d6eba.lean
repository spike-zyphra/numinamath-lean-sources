import Mathlib

theorem number_theory_124248 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^3 + y^4 = z^31} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (0, (2 : ℤ) ^ (n * (31 + 31 * n)), (2 : ℤ) ^ (n * (4 + 4 * n))))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    rcases h with ⟨h1, h2⟩
    have eq2 : (n : ℕ) = m := by
      have eq3 : (n * (n + 1) : ℕ) = m * (m + 1) := by
        have h1' : (n * (31 + 31 * n) : ℕ) = (m * (31 + 31 * m) : ℕ) := by
          omega
        have h3 : (n * (n + 1) : ℕ) = m * (m + 1) := by
          nlinarith
        exact h3
      -- Derive n = m from eq3 
      have h5 : n = m := by
        have eq4 : n ≤ m := by
          by_contra h
          push_neg at h
          have eq5 : (n * (n + 1) : ℕ) > (m * (m + 1) : ℕ) := by
            nlinarith [sq_nonneg ((n : ℤ) - (m : ℤ)), sq_nonneg ((n + m + 1 : ℤ))]
          omega
        have eq5 : m ≤ n := by
          by_contra h
          push_neg at h
          have eq6 : (m * (m + 1) : ℕ) > (n * (n + 1) : ℕ) := by
            nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((n + m + 1 : ℤ))]
          omega
        have h10 : n = m := by
          omega
        exact h10
      exact h5
    exact_mod_cast eq2
  · -- Show that all elements are in the set
    intro n
    simp [Prod.ext_iff]
    <;> ring_nf
    <;> norm_num
    all_goals
      ring