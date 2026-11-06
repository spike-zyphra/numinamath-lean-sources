import Mathlib

theorem number_theory_13397 :
    IsGreatest {k | ∃ n : ℕ, 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by
  constructor
  · -- Show that 486 is in the set, with n = 122
    use 122
    native_decide
  · -- Show that any k in the set is ≤ 486
    intro k hk
    rcases hk with ⟨n, hn⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 487 := by omega
    have eq : 3^11 = ∑ i in Finset.range k, (n + i) := hn
    have eq2 : ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by
      have h3 : ∀ (k' : ℕ), ∑ i in Finset.range k', (n + i) = k' * n + k' * (k' - 1) / 2 := by
        intro k'
        induction k' with
        | zero =>
          simp
        | succ k' ih =>
          rw [Finset.sum_range_succ, ih]
          cases k' with
          | zero =>
            simp
          | succ k' =>
            simp [Nat.mul_add, Nat.add_mul, mul_add]
            <;> ring_nf at *
            <;> omega
      exact h3 k
    rw [eq2] at eq
    have h2 : k ≤ 800 := by
      by_contra h
      push_neg at h
      have h3 : k ≥ 801 := by omega
      have h4 : k * (k - 1) / 2 > 3^11 := by
        have h5 : k ≥ 801 := by omega
        have h6 : k * (k - 1) ≥ 801 * 800 := by
          have h7 : k - 1 ≥ 800 := by omega
          nlinarith
        have h7 : k * (k - 1) / 2 ≥ (801 * 800) / 2 := by
          apply Nat.div_le_div
          all_goals
            omega
        omega
      -- Now using this inequality to contradict eq
      have h5 : k * n + k * (k - 1) / 2 > 3^11 := by
        have h6 : k * (k - 1) / 2 > 3^11 := h4
        omega
      omega
    interval_cases k <;> omega