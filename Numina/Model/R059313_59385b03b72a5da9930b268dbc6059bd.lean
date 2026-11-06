import Mathlib

theorem number_theory_218384 (n : ℕ) : ¬ 3 ∣ (n ^ 2 + 1) := by 
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
    omega 
  rcases h1 with (h | h | h)
  · -- Case where n % 3 = 0
    intro h2
    have h3 : (n ^ 2 + 1) % 3 = 1 := by 
      have hn : n % 3 = 0 := h
      have h3 : n ^ 2 % 3 = 0 := by 
        simp [Nat.pow_mod, hn]
      omega
    have h4 : (n ^ 2 + 1) % 3 = 0 := by 
      omega 
    omega 
  · -- Case where n % 3 = 1
    intro h2
    have h3 : (n ^ 2 + 1) % 3 = 2 := by 
      have hn : n % 3 = 1 := h
      have h1 : n ^ 2 % 3 = 1 := by 
        simp [Nat.pow_mod, hn]
      omega
    have h4 : (n ^ 2 + 1) % 3 = 0 := by 
      omega 
    omega 
  · -- Case where n % 3 = 2
    intro h2
    have h3 : (n ^ 2 + 1) % 3 = 2 := by 
      have hn : n % 3 = 2 := h
      have h1 : n ^ 2 % 3 = 1 := by 
        simp [Nat.pow_mod, hn]
      omega
    have h4 : (n ^ 2 + 1) % 3 = 0 := by 
      omega 
    omega