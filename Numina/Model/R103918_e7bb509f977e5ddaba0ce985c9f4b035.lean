import Mathlib

theorem number_theory_253630 (m n : ℕ) : 200 * m + 6 * n = 2006 ↔
    (m, n) = (1, 301) ∨ (m, n) = (4, 201) ∨ (m, n) = (7, 101) ∨ (m, n) = (10, 1) := by
  constructor
  · -- Assume $200 \cdot m + 6 \cdot n = 2006$, then $(m, n)$ must be one of the four pairs
    intro h
    have h1 : m ≤ 10 := by
      omega
    have h2 : m % 3 = 1 := by
      omega
    have h3 : m = 1 ∨ m = 4 ∨ m = 7 ∨ m = 10 := by
      omega
    rcases h3 with (r | r | r | r)
    · -- m = 1
      have hm : m = 1 := r
      have hn : n = 301 := by
        linarith [h, hm]
      left
      exact Prod.ext hm hn
    · -- m = 4
      have hm : m = 4 := r
      have hn : n = 201 := by
        linarith [h, hm]
      right
      left
      exact Prod.ext hm hn
    · -- m = 7
      have hm : m = 7 := r
      have hn : n = 101 := by
        linarith [h, hm]
      right
      right
      left
      exact Prod.ext hm hn
    · -- m = 10
      have hm : m = 10 := r
      have hn : n = 1 := by
        linarith [h, hm]
      right
      right
      right
      exact Prod.ext hm hn
  · -- Assume $(m, n)$ is one of the four pairs, then $200 \cdot m + 6 \cdot n = 2006$
    rintro (h | h | h | h)
    · -- (1, 301)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (4, 201)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (7, 101)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (10, 1)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num