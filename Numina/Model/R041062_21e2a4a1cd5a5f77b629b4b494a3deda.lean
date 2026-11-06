import Mathlib

theorem number_theory_290053 (n : ℕ) :
    7 ∣ 3^(2*n + 2) - 2^(n + 1) := by 
  have h1 : ∀ (n : ℕ), 3 ^ (2 * n + 2) % 7 = 2 ^ (n + 1) % 7 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num
    | succ n ih =>
      have eq1 : 3 ^ (2 * (n + 1) + 2) % 7 = (3 ^ (2 * n + 2) * 9) % 7 := by 
        ring_nf
      have eq2 : 2 ^ ((n + 1) + 1) % 7 = (2 ^ (n + 1) * 2) % 7 := by 
        ring_nf
      rw [eq1, eq2]
      simp [Nat.mul_mod, ih]
      <;> omega 
  have h_mod : 3 ^ (2 * n + 2) % 7 = 2 ^ (n + 1) % 7 := h1 n
  have h2 : (3 ^ (2 * n + 2) - 2 ^ (n + 1)) % 7 = 0 := by 
    have h3 : 3 ^ (2 * n + 2) % 7 = 2 ^ (n + 1) % 7 := h_mod
    have h4 : (3 ^ (2 * n + 2) - 2 ^ (n + 1)) % 7 = 0 := by 
      omega
    exact h4 
  exact Nat.dvd_of_mod_eq_zero h2