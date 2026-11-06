import Mathlib

theorem number_theory_10008 (n : ℕ) (hn : n > 0) :
    (∃ s : Fin n → ℕ, (∀ i, s i ∈ Finset.Icc 1 6) ∧ ∑ i, s i > 2 ^ n) ↔ n ≤ 4 := by
  constructor
  · -- Assume that there exists a sequence where the sum > 2^n, then n ≤ 4
    intro h
    rcases h with ⟨s, h1, h2⟩
    by_contra h3
    push_neg at h3
    have h4 : n ≥ 5 := by omega
    have h5 : ∑ i : Fin n, s i ≤ ∑ i : Fin n, 6 := by
      have h6 : ∀ i : Fin n, s i ≤ 6 := by
        intro i
        have h8 : s i ∈ Finset.Icc 1 6 := h1 i
        simp [Finset.mem_Icc] at h8 ⊢
        omega
      apply Finset.sum_le_sum
      intro i hi
      have h7 : s i ≤ 6 := h6 i
      omega
    have h8' : ∑ i : Fin n, (6 : ℕ) = 6 * n := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
    have h9 : ∑ i : Fin n, s i ≤ 6 * n := by
      linarith [h5, h8']
    have h10 : 2 ^ n ≥ 6 * n := by
      have h12 : ∀ (k : ℕ), 2 ^ (k + 5) ≥ 6 * (k + 5) := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_add, pow_one, mul_add] at ih ⊢
          omega
      specialize h12 (n - 5)
      have h13 : n - 5 + 5 = n := by omega
      rw [h13] at h12
      omega
    have h11 : ∑ i : Fin n, s i > 2 ^ n := h2
    omega
  · -- Assume n ≤ 4, prove the existence of s
    intro h_le
    have h1 : n ≤ 4 := by omega
    have h5 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      have h6 : n ≤ 4 := h1
      have h7 : n > 0 := hn
      interval_cases n <;> tauto
    rcases h5 with (r | r | r | r)
    · -- Case n = 1
      rw [show n = 1 by omega]
      use (λ _ => 3)
      constructor
      · -- Show that all elements are in [1, 6]
        intro i
        fin_cases i <;> simp [Finset.mem_Icc]
      · -- Show the sum > 2 ^ 1
        native_decide
    · -- Case n = 2
      rw [show n = 2 by omega]
      use λ i =>
        match i with
        | 0 => 4
        | 1 => 1
        | _ => 0
      constructor
      · -- Show that all elements are in [1, 6]
        intro i
        fin_cases i <;> simp [Finset.mem_Icc]
      · -- Show the sum > 2 ^ 2
        native_decide
    · -- Case n = 3
      rw [show n = 3 by omega]
      use λ i =>
        match i with
        | 0 => 6
        | 1 => 2
        | 2 => 1
        | _ => 0
      constructor
      · -- Show that all elements are in [1, 6]
        intro i
        fin_cases i <;> simp [Finset.mem_Icc]
      · -- Show the sum > 2 ^ 3
        native_decide
    · -- Case n = 4
      rw [show n = 4 by omega]
      use λ i =>
        match i with
        | 0 => 6
        | 1 => 6
        | 2 => 6
        | 3 => 6
        | _ => 0
      constructor
      · -- Show that all elements are in [1, 6]
        intro i
        fin_cases i <;> simp [Finset.mem_Icc]
      · -- Show the sum > 2 ^ 4
        native_decide