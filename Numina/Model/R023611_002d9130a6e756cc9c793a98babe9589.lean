import Mathlib

theorem number_theory_190891 :
    ¬∃ a b : ℕ, Odd a ∧ Odd b ∧ ∃ m n, a * b = m ^ 2 ∧ a + b = n ^ 2 := by 
  rintro ⟨a, b, h1, h2, ⟨m, n, h3, h4⟩⟩

  have h5 : a % 2 = 1 := by 
    rcases h1 with ⟨k, hk⟩ 
    omega

  have h6 : b % 2 = 1 := by 
    rcases h2 with ⟨l, hl⟩ 
    omega

  have h7 : (a + b) % 2 = 0 := by 
    omega

  have h8 : n % 2 = 0 := by 
    by_contra h 
    have h9 : n % 2 = 1 := by 
      omega 
    have h10 : (n ^ 2) % 2 = 1 := by 
      have h11 : n % 2 = 1 := h9 
      simp [Nat.pow_mod, h11] 
    have h11 : (a + b) % 2 = (n ^ 2) % 2 := by 
      omega 
    rw [h10] at h11 
    omega

  have h9 : ∃ k, n = 2 * k := by 
      refine' ⟨n / 2, by omega⟩ 
  rcases h9 with ⟨k, hk⟩ 
  have h10 : a + b = 4 * (k ^ 2) := by 
    rw [hk] at h4 
    have : a + b = (2 * k) ^ 2 := by linarith 
    nlinarith

  have h13 : (a * b) % 4 = 3 := by 
    have h15 : (a + b) % 4 = 0 := by 
      omega 
    have h16 : a % 4 = 1 ∨ a % 4 = 3 := by 
      omega 
    have h17 : b % 4 = 1 ∨ b % 4 = 3 := by 
      omega 
    have h18 : a % 4 = 1 → b % 4 = 3 := by 
      intro h 
      omega 
    have h19 : a % 4 = 3 → b % 4 = 1 := by 
      intro h 
      omega 
    have h20 : a % 4 = 1 ∨ a % 4 = 3 := h16 
    rcases h20 with (h20 | h20)
    · 
      have h21 : b % 4 = 3 := by 
        apply h18 
        exact h20 
      simp [Nat.mul_mod, h20, h21] 
    · 
      have h21 : b % 4 = 1 := by 
        apply h19 
        exact h20 
      simp [Nat.mul_mod, h20, h21] 

  -- m must be odd 
  have h14 : m % 2 = 1 := by 
    by_contra h15 
    have h16 : m % 2 = 0 := by 
      omega 
    have h17 : (m ^ 2) % 2 = 0 := by 
      have h18 : m % 2 = 0 := h16 
      simp [Nat.pow_mod, h18] 
    have h18 : (a * b) % 2 = 1 := by 
      have ha : a % 2 = 1 := h5 
      have hb : b % 2 = 1 := h6 
      simp [Nat.mul_mod, ha, hb] 
    have h19 : (a * b) % 2 = (m ^ 2) % 2 := by 
      omega 
    rw [h17] at h19 
    omega

  have h15b : (m ^ 2) % 4 = 1 := by
    have h12' : m % 2 = 1 := h14 
    have h16 : m % 4 = 1 ∨ m % 4 = 3 := by 
      omega 
    rcases h16 with (h | h)
    · 
      simp [Nat.pow_mod, h] 
    · 
      simp [Nat.pow_mod, h] 

  -- m^2 % 4 
  have h15c : (a * b) % 4 = (m ^ 2) % 4 := by 
    omega 
  rw [h15b] at h15c
  omega