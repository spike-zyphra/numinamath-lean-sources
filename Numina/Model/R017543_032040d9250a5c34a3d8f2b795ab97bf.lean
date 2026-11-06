import Mathlib

def A (n : ℕ) := ∃ k, n = ∑ i ∈ Finset.range 7, (k + i)

def B (n : ℕ) := ∃ k, n = ∑ i ∈ Finset.range 8, (k + i)

def C (n : ℕ) := ∃ k, n = ∑ i ∈ Finset.range 9, (k + i)

theorem number_theory_4007 :
    {n | A n ∧ B n ∧ C n} = {n | ∃ m, n = 504 * m + 252} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume n ∈ A ∧ n ∈ B ∧ n ∈ C, prove ∃ m, n = 504 * m + 252
    rintro ⟨ha, hb, hc⟩
    rcases ha with ⟨k, h7⟩
    have h7k : n = 7 * (k + 3) := by
      norm_num [Finset.sum_range_succ] at h7 ⊢
      omega
    rcases hb with ⟨k, h8⟩
    have h8k : n = 8 * k + 28 := by
      norm_num [Finset.sum_range_succ] at h8 ⊢
      omega
    rcases hc with ⟨k, h9⟩
    have h9k : n = 9 * (k + 4) := by
      norm_num [Finset.sum_range_succ] at h9 ⊢
      omega
    have hmod7 : n % 7 = 0 := by
      omega
    have hmod8 : n % 8 = 4 := by
      omega
    have hmod9 : n % 9 = 0 := by
      omega
    have h1 : n % 7 = 0 := hmod7
    have h2 : n % 9 = 0 := hmod9
    have h3 : n % 63 = 0 := by
      omega
    have h4 : ∃ t, n = 63 * t := by
      refine' ⟨n / 63, by omega⟩
    rcases h4 with ⟨t, ht⟩
    have h5 : (63 * t) % 8 = 4 := by
      omega
    have htmod8 : t % 8 = 4 := by
      omega
    refine' ⟨t / 8, by omega⟩
  · -- Assume ∃ m, n = 504 * m + 252, prove A n ∧ B n ∧ C n
    rintro ⟨m, hm⟩
    constructor
    · -- Show n ∈ A
      use (n / 7 - 3)
      have h1 : n % 7 = 0 := by
        omega
      have h2 : n = 7 * ((n / 7) ) := by
        omega
      norm_num [Finset.sum_range_succ] at *
      <;> omega
    constructor
    · -- Show n ∈ B
      use (63 * m + 28)
      norm_num [Finset.sum_range_succ] at *
      <;> omega
    · -- Show n ∈ C
      use (n / 9 - 4)
      have h4 : n % 9 = 0 := by
        omega
      have h5 : n = 9 * (n / 9) := by
        omega
      norm_num [Finset.sum_range_succ] at *
      <;> omega