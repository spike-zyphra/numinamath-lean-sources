import Mathlib

theorem other_76000 (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 1)
    (h₂ : ∀ n, a (n + 2) = (n * (n + 1) * a (n + 1) + n ^ 2 * a n + 5) / (n + 2) - 2) :
    {n : ℕ | n ≥ 1 ∧ ∃ m : ℕ, a n = m} = {1, 2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n ≥ 1 and exists m : ℕ, a n = m then n = 1 or n = 2
    intro h
    rcases h with ⟨hn, m, hm⟩
    have h3 := h₂ 0
    have h4 : a 2 = (0 * (0 + 1) * a 1 + 0 ^ 2 * a 0 + 5) / (0 + 2) - 2 := by
      simpa using h3
    rw [show a 1 = (1 : ℝ) by linarith [h₀]] at h4
    have h5 : a 2 = (5 : ℝ) / 2 - 2 := by
      norm_num at h4 ⊢
      linarith [h4]
    have h6 : a 2 = (1 : ℝ) := by
      linarith [h₁]
    rw [h6] at h5
    norm_num at h5
  · -- Second direction: n = 1 or n = 2 implies n ∈ {n : ℕ | n ≥ 1 ∧ ∃ m : ℕ, a n = m}
    rintro (rfl | rfl)
    · -- Case n = 1
      constructor
      · norm_num
      · use 1
        norm_num [h₀]
    · -- Case n = 2
      constructor
      · norm_num
      · use 1
        norm_num [h₁]