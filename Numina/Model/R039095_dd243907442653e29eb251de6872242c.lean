import Mathlib


open Nat


lemma lemma_1 (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    2 * n + k - 1 > k := by
  have h1 : 2 * n > 1 := by
    omega
  omega


theorem number_theory_190193 :
    IsGreatest {k | ∃ n : ℕ, 0 < n ∧ 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by
  constructor
  · -- 486 is achievable
    use 122
    native_decide
  · -- 486 is greatest
    intro k
    intro hk
    rcases hk with ⟨n, hn, h_eq⟩
    have h1 : ∀ k n : ℕ, 3^11 = ∑ i in Finset.range k, (n + i) → k * n + (k * (k - 1)) / 2 = 3^11 := by
      intro k n h_eq
      have h2 : ∀ k : ℕ, ∑ i in Finset.range k, (n + i) = k * n + (k * (k - 1)) / 2 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          cases k with
          | zero =>
            omega
          | succ k =>
            simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, mul_comm] at *
            <;> ring_nf <;> omega
      have h3 : ∑ i in Finset.range k, (n + i) = k * n + (k * (k - 1)) / 2 := h2 k
      omega
    have h_eq2 : k * n + (k * (k - 1)) / 2 = 3^11 := by
      apply h1 k n h_eq
    by_contra h
    push_neg at h
    have h4 : k ≤ 729 := by
      by_contra h
      push_neg at h
      have h5 : k * (k - 1) / 2 ≥ 177148 := by
        have h6 : k ≥ 730 := by
          omega
        have h7 : k - 1 ≥ 729 := by
          omega
        have h7' : k * (k - 1) ≥ 730 * 729 := by
          nlinarith
        omega
      have h6 : k * n ≤ 0 := by
        omega
      have h7 : k * n ≥ k := by
        nlinarith
      nlinarith
    interval_cases k <;> omega