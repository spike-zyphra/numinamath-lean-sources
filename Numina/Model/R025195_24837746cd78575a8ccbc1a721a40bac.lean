import Mathlib

theorem number_theory_275539 (n : ℕ) (h₀ : Even n) (h₁ : Even (n + 2)) :
    8 ∣ n * (n + 2) := by
  rcases h₀ with ⟨k, hk⟩ 
  have h2 : n + 2 = 2 * (k + 1) := by 
    rw [hk]
    all_goals ring
  have eq1 : n * (n + 2) = 4 * (k * (k + 1)) := by 
    rw [h2, hk]
    ring
  have h3 : k * (k + 1) % 2 = 0 := by
    have h4 : k % 2 = 0 ∨ k % 2 = 1 := by 
      omega
    rcases h4 with (h4 | h4)
    · 
      simp [Nat.mul_mod, Nat.add_mod, h4]
    · 
      simp [Nat.mul_mod, Nat.add_mod, h4]
  have h4 : ∃ t, k * (k + 1) = 2 * t := by
    have h5 : k * (k + 1) % 2 = 0 := h3 
    refine' ⟨(k * (k + 1)) / 2, by
      omega
    ⟩
  rcases h4 with ⟨t, ht⟩ 
  have eq2 : n * (n + 2) = 8 * t := by 
    calc 
      n * (n + 2) = 4 * (k * (k + 1)) := by 
        rw [eq1]
      _ = 4 * (2 * t) := by 
        rw [ht]
      _ = 8 * t := by 
        ring
  -- final goal
  exact ⟨t, by linarith [eq2]⟩