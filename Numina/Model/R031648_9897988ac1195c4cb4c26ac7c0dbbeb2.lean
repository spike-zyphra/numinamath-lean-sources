import Mathlib

theorem number_theory_280874 (n : ℕ) (h : ¬ 3 ∣ n + 1) :
    9 * (n + 1) ∣ (n^3 + (n + 1)^3 + (n + 2)^3) := by 
  have h1 : n % 3 = 0 ∨ n % 3 = 1 := by
    omega
  have h2 : (n^3 + (n + 1)^3 + (n + 2)^3) = 3 * (n + 1) * (n^2 + 2 * n + 3) := by 
    ring
  have h3 : (n^2 + 2 * n + 3) % 3 = 0 := by
    rcases h1 with (h1 | h1)
    · -- n % 3 = 0
      have h4 : n % 3 = 0 := h1
      have h5 : (n ^ 2 + 2 * n + 3) % 3 = 0 := by
        simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h4]
      omega 
    · -- n % 3 = 1
      have h4 : n % 3 = 1 := h1
      have h5 : (n ^ 2 + 2 * n + 3) % 3 = 0 := by
        simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h4]
      omega 
  have h4 : 9 * (n + 1) ∣ (n^3 + (n + 1)^3 + (n + 2)^3) := by
    rw [h2]
    have h6 : 9 ∣ 3 * (n ^ 2 + 2 * n + 3) := by 
      omega 
    have h7 : 9 * (n + 1) ∣ 3 * (n + 1) * (n ^ 2 + 2 * n + 3) := by 
      have h8 : 9 ∣ 3 * (n ^ 2 + 2 * n + 3) := h6 
      have h9 : 9 * (n + 1) ∣ 3 * (n ^ 2 + 2 * n + 3) * (n + 1) := by 
        apply mul_dvd_mul_right 
        exact h8 
      ring_nf at h9 ⊢ 
      all_goals omega 
    exact h7 
  exact h4