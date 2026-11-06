import Mathlib

theorem algebra_316861 (k : ℤ) :
    IsLeast {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} (4 * k + 106) ↔
    -9 ≤ k ∧ k ≤ -7 := by
  constructor
  · -- Assume IsLeast, prove -9 ≤ k ∧ k ≤ -7
    intro h
    have h1 : 4 * k + 106 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := h.1
    have h2 : ∀ x, x ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} → 4 * k + 106 ≤ x := h.2
    have h_k1 : k + 91 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨1, by ring_nf, by norm_num, by norm_num⟩
    have h_k2 : 2 * k + 94 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨2, by ring_nf, by norm_num, by norm_num⟩
    have h_k3 : 3 * k + 99 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨3, by ring_nf, by norm_num, by norm_num⟩
    have h_k5 : 5 * k + 115 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨5, by ring_nf, by norm_num, by norm_num⟩
    have h_k6 : 6 * k + 126 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨6, by ring_nf, by norm_num, by norm_num⟩
    have h_k7 : 7 * k + 139 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨7, by ring_nf, by norm_num, by norm_num⟩
    have h_k8 : 8 * k + 154 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨8, by ring_nf, by norm_num, by norm_num⟩
    have h_k9 : 9 * k + 171 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨9, by ring_nf, by norm_num, by norm_num⟩
    have h_k10 : 10 * k + 190 ∈ {x | ∃ n, x = n^2 + k * n + 90 ∧ 1 ≤ n ∧ n ≤ 10} := by
      refine' ⟨10, by ring_nf, by norm_num, by norm_num⟩
    have h4 : 4 * k + 106 ≤ k + 91 := by
      specialize h2 (k + 91) h_k1
      linarith
    have h5 : 4 * k + 106 ≤ 2 * k + 94 := by
      specialize h2 (2 * k + 94) h_k2
      linarith
    have h6 : 4 * k + 106 ≤ 3 * k + 99 := by
      specialize h2 (3 * k + 99) h_k3
      linarith
    have h7 : 4 * k + 106 ≤ 5 * k + 115 := by
      specialize h2 (5 * k + 115) h_k5
      linarith
    have h8 : 4 * k + 106 ≤ 6 * k + 126 := by
      specialize h2 (6 * k + 126) h_k6
      linarith
    have h9 : 4 * k + 106 ≤ 7 * k + 139 := by
      specialize h2 (7 * k + 139) h_k7
      linarith
    have h10 : 4 * k + 106 ≤ 8 * k + 154 := by 
      specialize h2 (8 * k + 154) h_k8
      linarith
    have h11 : 4 * k + 106 ≤ 9 * k + 171 := by
      specialize h2 (9 * k + 171) h_k9
      linarith
    have h12 : 4 * k + 106 ≤ 10 * k + 190 := by
      specialize h2 (10 * k + 190) h_k10
      linarith
    constructor
    · -- Prove k ≥ -9
      omega
    · -- Prove k ≤ -7
      omega
  · -- Assume -9 ≤ k ∧ k ≤ -7, prove IsLeast
    rintro ⟨hk1, hk2⟩
    constructor
    · -- Show 4k + 106 is in the set
      refine' ⟨4, by ring_nf, by norm_num, by norm_num⟩
    · -- Show minimality
      intro x hx
      rcases hx with ⟨n, hx_eq, hn1, hn2⟩
      have : n ≥ 1 := by linarith
      have : n ≤ 10 := by linarith
      interval_cases n <;> nlinarith