import Mathlib
/-let m be the smallets positive integer such that m^2+...+(m+10)^2 is the square of a positive integer n. Find m+n-/
theorem number_theory_57495 {m n : ℕ} (hm : IsLeast {x : ℕ | 0 < x ∧ ∃ k : ℕ, ∑ i ∈ Finset.range 11, (x + i)^2 = k^2} m)
    (hn : 0 < n ∧ ∑ i ∈ Finset.range 11, (m + i)^2 = n^2) : m + n = 95 := by
  -- first show that m > 0
  have h1 : m > 0 := by
    rcases hm with ⟨⟨h1, _⟩, _⟩
    exact h1
  rcases hn with ⟨hn_pos, hn_eq⟩
  rcases hm with ⟨⟨hm_pos, hm_in⟩, hm_min⟩
  have h2 : ∃ k, ∑ i in Finset.range 11, (m + i) ^ 2 = k ^ 2 := hm_in
  rcases h2 with ⟨k, hk_eq⟩
  have h3 : m ≥ 18 := by  -- prove by directly check
    by_contra h
    push_neg at h
    have : m ≤ 17 := by linarith
    interval_cases m <;> try { 
      simp [Finset.sum_range_succ] at hk_eq hn_eq 
      ( 
        have : k ≤ 100 := by nlinarith 
        interval_cases k <;> omega 
      )
    }
  have h4 : m ≤ 18 := by   -- prove by show 18 is right
    have h5 : 18 ∈ {x : ℕ | 0 < x ∧ ∃ k : ℕ, ∑ i ∈ Finset.range 11, (x + i) ^ 2 = k ^ 2} := by
      constructor
      · norm_num
      · use 77
        norm_num [Finset.sum_range_succ]
    exact hm_min h5 
  have hm_eq : m = 18 := by linarith
  have hn_eq' : n = 77 := by -- finally compute n
    rw [hm_eq] at hn_eq
    norm_num [Finset.sum_range_succ] at hn_eq
    nlinarith
  linarith [hm_eq, hn_eq']