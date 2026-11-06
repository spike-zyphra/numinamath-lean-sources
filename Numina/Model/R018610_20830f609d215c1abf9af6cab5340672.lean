import Mathlib

theorem number_theory_154099 (T : ℕ → ℕ)
    (hT : ∀ n, T n = n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2) :
    {n | 10 ∣ T n} = {n | ∃ m, n = 5 * m + 1} := by 
  ext n 
  simp only [hT, Set.mem_setOf_eq]
  constructor
  · -- Let's prove the forward direction
    intro h
    have h2 : (n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2) % 10 = 0 := by 
      omega
    have h1 : n % 5 = 1 := by 
      have h3 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by 
        omega 
      rcases h3 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [h4, Nat.add_mod, Nat.mul_mod, pow_two, Nat.pow_mod] at h2 ⊢ 
      <;> omega 
    have h4 : ∃ m, n = 5 * m + 1 := by 
      have h5 : n % 5 = 1 := h1 
      have : ∃ m, n = 5 * m + 1 := by 
        refine' ⟨(n - 1) / 5, by omega⟩ 
      exact this 
    exact h4 
  · -- Now the reverse direction
    intro h 
    rcases h with ⟨m, hm⟩ 
    rw [hm] 
    have h10 : ( (5 * m + 1) ^ 2 + (5 * m + 1 + 1) ^ 2 + (5 * m + 1 + 2) ^ 2 + (5 * m + 1 + 3) ^ 2 ) % 10 = 0 := by 
      ring_nf 
      omega 
    omega 
    all_goals try omega 
    all_goals omega