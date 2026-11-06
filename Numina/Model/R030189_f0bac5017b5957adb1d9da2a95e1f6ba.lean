import Mathlib

theorem number_theory_301961 {a d : ℤ} (hd : d ≠ 0) (ha : ∀ n, 0 < a + d * n)
    (h : ∃ n, ∃ m, a + d * n = m ^ 2) :
    {x | ∃ n, x = a + d * n ∧ ∃ m, x = m ^ 2}.Infinite := by
  have h3 : d ≠ 0 := hd
  have h4 := ha ((0 - a) / d)
  have h5 : a + d * ((0 - a) / d) ≤ 0 := by
    have h8 : a + d * ((0 - a) / d) = - ((0 - a) % d) := by
      have h9 : (0 - a) = d * ((0 - a) / d) + ((0 - a) % d) := by
        rw [Int.ediv_add_emod (0 - a) d]
      nlinarith
    have h6 : ((0 - a) % d) ≥ 0 := by
      have h7 : ((0 - a) % d) ≥ 0 := by
        apply Int.emod_nonneg
        omega
      omega
    linarith [h8, h6]
  nlinarith