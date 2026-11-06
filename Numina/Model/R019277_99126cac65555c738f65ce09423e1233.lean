import Mathlib

theorem number_theory_12025 (n : ℕ) (h₀ : n > 0) :
    (∃ k, ∑ i in Finset.Icc 1 n, i = k ∧ k ∈ Finset.Icc 100 999 ∧
      ∃ m, k = m * 111) ↔ n = 36 := by
  constructor
  · -- Assume (∃ k, ∑ i in Finset.Icc 1 n, i = k ∧ k ∈ Finset.Icc 100 999 ∧
    --     ∃ m, k = m * 111)
    -- Prove n = 36
    rintro ⟨k, h_eq_k, hk_dig, m, h_eq_m⟩
    have h7 : ∑ i in Finset.Icc 1 n, i = k := h_eq_k
    have h8 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
      intro n
      have h1 : ∀ (k : ℕ), ∑ i in Finset.Icc 1 k, i = k * (k + 1) / 2 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          rw [ih]
          ring_nf
          omega
      specialize h1 n
      simpa using h1
    have h6 : n * (n + 1) / 2 = k := by
      have h7 : ∑ i in Finset.Icc 1 n, i = k := h_eq_k
      rw [h8 n] at h7
      omega
    have h9 : k = m * 111 := by
      omega
    rw [h9] at h6
    have h2 : k ∈ Finset.Icc 100 999 := by
      exact hk_dig
    rw [Finset.mem_Icc] at h2
    rcases h2 with ⟨h2l, h2u⟩
    have h4 : m ≥ 1 := by
      omega
    have h5 : m ≤ 9 := by
      omega
    interval_cases m <;> try { 
      have : n ≤ 50 := by 
        by_contra h
        push_neg at h
        have h10 : n * (n + 1) / 2 > 999 := by
          have : n ≥ 51 := by omega
          have : n * (n + 1) ≥ 51 * 52 := by nlinarith [show (n) ≥ 51 from by omega]
          omega
        omega
      interval_cases n <;> omega 
    }
  · -- Assume n = 36, prove (∃ k, ∑ i in Finset.Icc 1 n, i = k ∧ k ∈ Finset.Icc 100 999 ∧
    --     ∃ m, k = m * 111)
    intro h
    rw [h]
    use 666
    constructor
    · -- Show that the sum is k
      native_decide
    constructor
    · -- Show that k ∈ [100, 999]
      native_decide
    · -- Show that exists m, k = m * 111
      use 6
      all_goals omega