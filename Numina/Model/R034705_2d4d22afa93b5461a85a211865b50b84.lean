import Mathlib

theorem number_theory_8989 (n : ℕ) (hn : n > 0) (h : ∃ m, m^2 = 3 * n + 1) :
    ∃ a b c, a^2 + b^2 + c^2 = n + 1 := by 
  rcases h with ⟨m, hm⟩ 
  have h1 : m^2 = 3 * n + 1 := by linarith 
  have h2 : m % 3 = 1 ∨ m % 3 = 2 := by
    have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
      omega 
    rcases h3 with (h3 | h3 | h3)
    · -- Case m % 3 = 0
      -- This would imply $m^2 \equiv 0 \pmod{3}$, which contradicts $m^2 \equiv 1 \pmod{3}$
      have h4 : m ^ 2 % 3 = 0 := by
        simp [Nat.pow_mod, h3]
      -- But $3 * n + 1 \equiv 1 \pmod{3}$, so $m^2 \equiv 1 \pmod{3}$
      have h5 : m ^ 2 % 3 = 1 := by
        omega 
      omega 
    · -- Case m % 3 = 1
      left 
      omega 
    · -- Case m % 3 = 2
      right 
      omega 
  rcases h2 with (h2 | h2)
  · -- Case m % 3 = 1
    have h3 : ∃ k, m = 3 * k + 1 := by 
      have : m % 3 = 1 := h2 
      refine ⟨m / 3, by omega⟩ 
    rcases h3 with ⟨k, hk⟩ 
    have eq1 : 3 * n + 1 = (3 * k + 1) ^ 2 := by 
      rw [hk] at hm 
      linarith 
    have eq2 : n = 3 * k ^ 2 + 2 * k := by
      nlinarith [eq1] 
    use k, k, k + 1 
    rw [eq2] 
    all_goals ring_nf 
  · -- Case m % 3 = 2
    have h3 : ∃ k, m = 3 * k + 2 := by
      have : m % 3 = 2 := h2 
      refine ⟨m / 3, by omega⟩ 
    rcases h3 with ⟨k, hk⟩ 
    have eq1 : 3 * n + 1 = (3 * k + 2) ^ 2 := by 
      rw [hk] at hm 
      linarith 
    have eq2 : n = 3 * k ^ 2 + 4 * k + 1 := by
      nlinarith [eq1] 
    use k, k + 1, k + 1 
    rw [eq2] 
    all_goals ring_nf