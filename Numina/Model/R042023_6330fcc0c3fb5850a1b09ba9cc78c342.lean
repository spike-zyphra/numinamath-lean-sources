import Mathlib
theorem Number_theory_609399: IsLeast {N: ℕ | (N > 1) ∧ (∃ a ≥ 1, N = a * (2 * a - 1)) ∧ (∀ k : ℕ, 1 ≤ k ∧ k ≤ 10 → (N * (N - 1)) % (2 * k) = 0)} 2016 := by
  constructor
  · -- Show that 2016 is in the set
    constructor
    · -- Show that 2016 > 1
      norm_num
    constructor
    · -- Show that there exists a ≥ 1, 2016 = a * (2 * a - 1)
      use 32
      all_goals
        norm_num
    · -- Show that ∀ k : ℕ, 1 ≤ k ∧ k ≤ 10 → (2016 * (2016 - 1)) % (2 * k) = 0
      intro k hk
      rcases hk with ⟨hk1, hk10⟩
      interval_cases k <;> norm_num at *
  · -- Show that 2016 is the least
    intro N h
    rcases h with ⟨hN1, ⟨a, ha, hN2⟩, h⟩
    by_contra h'
    push_neg at h'
    have hN3 : N < 2016 := by linarith
    have h1 := h 7 ⟨by norm_num, by norm_num⟩
    have h2 := h 9 ⟨by norm_num, by norm_num⟩
    have h3 := h 5 ⟨by norm_num, by norm_num⟩
    have h4 := h 4 ⟨by norm_num, by norm_num⟩
    have h5 := h 8 ⟨by norm_num, by norm_num⟩
    have h6 := h 10 ⟨by norm_num, by norm_num⟩
    have h7 := h 3 ⟨by norm_num, by norm_num⟩
    have h8 := h 6 ⟨by norm_num, by norm_num⟩
    have h9 := h 2 ⟨by norm_num, by norm_num⟩
    have h10 := h 1 ⟨by norm_num, by norm_num⟩
    have h11 : a ≤ 32 := by
      by_contra h'
      push_neg at h'
      have : a ≥ 33 := by linarith
      have : a * (2 * a - 1) ≥ 2016 := by
        have : a ≥ 33 := by linarith
        have h1 : 2 * a - 1 ≥ 65 := by omega
        have h2 : a * (2 * a - 1) ≥ 33 * 65 := by
          have h3 : a ≥ 33 := by linarith
          have h4 : 2 * a - 1 ≥ 65 := by omega
          nlinarith
        norm_num at h2 ⊢
        linarith
      omega
    interval_cases a <;> try { norm_num [hN2] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hN1 hN3 } <;> omega