import Mathlib

theorem number_theory_153913 (n : ℕ) :
    n ∈ Finset.Icc 1 999 ∧ (Nat.digits 10 n).sum^3 = n^2 ↔ n = 1 ∨ n = 27 := by
  constructor
  · -- First implication.
    intro h
    rcases h with ⟨h1, h2⟩
    rw [Finset.mem_Icc] at h1
    rcases h1 with ⟨h1l, h1u⟩
    interval_cases n <;> norm_num at h2 ⊢
    <;> omega
  · -- Second implication.
    rintro (h | h)
    · -- Case n = 1
      rw [h]
      constructor
      · -- Show that 1 is in the range [1, 999]
        simp
      · -- Verify the equation for n=1
        all_goals norm_num
    · -- Case n = 27
      rw [h]
      constructor
      · -- Show that 27 is in the range [1, 999]
        simp
      · -- Verify the equation for n=27
        all_goals norm_num