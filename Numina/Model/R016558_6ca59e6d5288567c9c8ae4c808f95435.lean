import Mathlib

theorem number_theory_154747 : IsGreatest {x | x^2 ∣ (24 * 35 * 46 * 57)} 12 := by
  constructor
  · -- Show that 12 is in the set
    norm_num
  · -- Show that 12 is greatest
    intro x hx
    have h1 : x ^ 2 ∣ (24 * 35 * 46 * 57 : ℕ) := by
      simpa using hx
    by_contra h
    push_neg at h
    have h2 : x ≤ 31 := by
      by_contra h
      push_neg at h
      have h4 : x ≥ 32 := by omega
      have h5 : x ^ 2 ∣ (24 * 35 * 46 * 57 : ℕ) := h1
      have h6 : x ^ 2 ≤ (24 * 35 * 46 * 57 : ℕ) := by
        exact Nat.le_of_dvd (by norm_num) h5
      have h7 : x ≤ 1484 := by
        nlinarith
      interval_cases x <;> norm_num at h1 ⊢
      <;> try { contradiction }
      <;> ring_nf at *
      <;> try { contradiction }
    interval_cases x <;> norm_num at h1 ⊢
    <;> try { contradiction }
    <;> ring_nf at *
    <;> try { contradiction }
    <;> omega
  all_goals
    tauto