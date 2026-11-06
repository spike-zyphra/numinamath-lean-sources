import Mathlib

theorem number_theory_293176 (s : ℕ) (m : ℕ → ℕ) (h₀ : s ≥ 2)
    (h₁ : ∀ i ∈ Finset.Icc 1 s, m i > 0) (h₂ : ∀ i ∈ Finset.Icc 1 s,
    ∀ j ∈ Finset.Icc 1 s, i ≠ j → ¬∃ k : Finset ℕ, ∑ l ∈ k, m l = m i + m j) :
    ∀ r ∈ Finset.Ico 1 s, r * m r + m s ≥ (r + 1) * (s - 1) := by

  have h3 := h₂ 1 (by
    have h11 : 1 ≤ 1 := by linarith
    have h12 : 1 ≤ s := by linarith
    simp [Finset.mem_Icc] at *
    all_goals linarith) 2 (by
    have h21 : 1 ≤ 2 := by linarith
    have h22 : 2 ≤ s := by
      omega
    simp [Finset.mem_Icc] at *
    all_goals linarith) (by norm_num)

  have h4 : ∃ k : Finset ℕ, ∑ l ∈ k, m l = m 1 + m 2 := by
    use {1, 2}
    simp [Finset.sum_insert, Finset.sum_singleton]
    all_goals linarith

  contradiction