import Mathlib

def is_stutterer (n : ℕ) : Prop :=
  n ∈ Finset.Icc 1000 9999 ∧ (n / 100) % 11 = 0 ∧ (n % 11) % 11 = 0

theorem number_theory_54945 :
    {n | ∃ k, n = k^2 ∧ is_stutterer n} = {7744} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the left side, prove n = 7744
    rintro ⟨k, rfl, hk⟩
    rcases hk with ⟨h1, h2, h3⟩
    rw [Finset.mem_Icc] at h1
    rcases h1 with ⟨h4, h5⟩
    have h6 : k ≤ 99 := by
      nlinarith
    have h7 : k ≥ 32 := by
      nlinarith
    interval_cases k <;> norm_num [is_stutterer, Finset.mem_Icc] at *
    <;> omega
  · -- Assume n = 7744, prove n is in the left side
    intro h
    rw [h]
    use 88
    all_goals norm_num [is_stutterer, Finset.mem_Icc]
    <;> tauto