import Mathlib

theorem number_theory_187033 :
    Set.Infinite {(l, m, n) : ℕ × ℕ × ℕ | l ^ 2 + m ^ 2 = n ^ 2 + 3} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 * (t + 1), 2 * (t + 1) ^ 2 - 2, 2 * (t + 1) ^ 2 - 1))
  · -- Show f is injective
    intro t1 t2 h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements in the image are in the set
    intro t
    have eq1 : (2 * (t + 1) : ℕ) ^ 2 + (2 * (t + 1) ^ 2 - 2 : ℕ) ^ 2 = (2 * (t + 1) ^ 2 - 1 : ℕ) ^ 2 + 3 := by
      have h1 : 2 * (t + 1) ^ 2 ≥ 2 := by
        have h7 : (t + 1) ^ 2 ≥ 1 := by
          have h8 : t + 1 ≥ 1 := by
            omega
          nlinarith
        nlinarith
      have h2 : 2 * (t + 1) ^ 2 ≥ 1 := by
        have h7 : (t + 1) ^ 2 ≥ 1 := by
          have h8 : t + 1 ≥ 1 := by
            omega
          nlinarith
        nlinarith
      have h3 : (2 * (t + 1) ^ 2 : ℕ) ≥ 2 := h1
      have h4 : (2 * (t + 1) ^ 2 - 2 : ℕ) = (2 * (t + 1) ^ 2 : ℕ) - 2 := by
        omega
      have h5 : (2 * (t + 1) ^ 2 - 1 : ℕ) = (2 * (t + 1) ^ 2 : ℕ) - 1 := by
        omega
      rw [h4, h5]
      zify [show (2 * (t + 1) ^ 2 : ℕ) ≥ 2 by omega, show (2 * (t + 1) ^ 2 : ℕ) ≥ 1 by omega]
      ring_nf
    simp_all [Prod.ext_iff]