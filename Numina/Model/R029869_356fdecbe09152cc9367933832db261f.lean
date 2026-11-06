import Mathlib

theorem number_theory_46455 (a : ℕ → ℕ) (ha : ∀ m n, 0 < a m ∧ 0 < a n)
    (h1 : ∀ m n, a m * a n = a (m * n)) (h2 : ∀ N, ∃ n, n > N ∧
    ∃ p : Equiv.Perm ℕ, ∀ i ∈ Finset.Icc 1 n, a i = p i) :
    ∀ n, 0 < n → a n = n := by
  have h0 := h1 0 0
  have h4 := ha 0 0 
  have h6 : a 0 = 1 := by
    have h7 : a 0 * a 0 = a (0 * 0) := by
      apply h1
    have h7' : a (0 * 0) = a 0 := by
      simp
    rw [h7'] at h7
    nlinarith
  have h10 : ∀ n : ℕ, a n = 1 := by
    intro n
    have h11 : a 0 * a n = a (0 * n) := by
      apply h1
    have h14 : a (0 * n) = a 0 := by
      simp
    have h15 := h6
    have h18 : a 0 * a n = a 0 := by
      rw [h14] at h11
      linarith
    have h20 : a 0 = 1 := h6
    rw [h20] at h18
    have hn1 : a n = 1 := by
      nlinarith
    exact hn1
  have h21 := h2 2
  rcases h21 with ⟨n, hn2, p, hp⟩
  have hp1 := hp 1 (by
    simp at *
    <;> omega
  )
  have hp2 := hp 2 (by
    have hx1 : 1 ≤ (2 : ℕ) := by omega
    have hx2 : 2 ≤ (n : ℕ) := by omega
    simp [hx1, hx2]
    all_goals linarith
  )
  have h24 : p 1 = 1 := by
    linarith [hp1, h10 1]
  have h25 : p 2 = 1 := by
    linarith [hp2, h10 2]
  have h26 : p 1 ≠ p 2 := by
    intro heq
    have h17 : (1 : ℕ) = (2 : ℕ) := by
      have h18 : p 1 = p 2 := by 
        linarith [heq]
      have h19 : (1 : ℕ) = (2 : ℕ) := by
        apply p.injective
        all_goals
        try { tauto }
        try { linarith }
        try { contradiction }
        try { tauto }
      exact h19
    omega
  have h27 : p 1 = p 2 := by
    omega
  contradiction
  all_goals try { contradiction }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { linarith }
  all_goals try { tauto }