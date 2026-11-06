import Mathlib

theorem number_theory_29121 :
    { x | ∃ a b n : ℕ, 1 ≤ a ∧  a ≤ 9 ∧  b ≤ 9 ∧ 1000 ≤ x ∧  x ≤ 9999 ∧ x = 1000 * a + 100 * b + 10 * a + b ∧ x = n ^ 2 + 1 } = {8282}  := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First prove that if x in the set, x = 8282
    rintro ⟨a, b, n, ha1, ha2, hb1, hx1, hx2, heq1, heq2⟩
    have h1 : x = 1010 * a + 101 * b := by
      omega
    have h2 : x % 101 = 0 := by
      have h3 : x = 1010 * a + 101 * b := h1
      have h4 : x = 101 * (10 * a + b) := by
        omega
      omega
    have h3 : n ≤ 99 := by
      nlinarith [heq2, hx1, hx2]
    have h4 : n ≥ 32 := by
      nlinarith [heq2, hx1, hx2]
    interval_cases n <;> omega
  · -- Now prove the converse: if x = 8282, x is in the set
    intro heq2
    rw [heq2]
    use 8, 2, 91
    all_goals norm_num