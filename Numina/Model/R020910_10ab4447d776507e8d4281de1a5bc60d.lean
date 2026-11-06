import Mathlib

theorem number_theory_114452 (a : ℕ) :
    ∃ x y, a^3 = (x^2 - y^2) := by 
  use (a ^ 2 + a) / 2, (a ^ 2 - a) / 2
  have h1 : ∀ a : ℕ, (a ^ 2 + a) % 2 = 0 := by
    intro a 
    have h2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h2 with (h | h)
    · -- if a is even
      simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod]
    · -- if a is odd
      simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod]
  have h2 : ∀ a : ℕ, (a ^ 2 - a) % 2 = 0 := by 
    intro a
    have h3 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h3 with (h | h)
    · -- if a is even 
      simp [Nat.sub_mod_eq_zero_of_mod_eq, Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod]
      <;> omega
    · -- if a is odd 
      simp [Nat.sub_mod_eq_zero_of_mod_eq, Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod]
      <;> omega
  have eq1 : ((a ^ 2 + a) / 2 : ℕ) ^ 2 - ((a ^ 2 - a) / 2 : ℕ) ^ 2 = a^3 := by 
    have h3 : ((a ^ 2 + a) / 2 : ℕ) * 2 = a^2 + a := by 
      have h2' : (a ^ 2 + a) % 2 = 0 := h1 a
      omega
    have h4 : ((a ^ 2 - a) / 2 : ℕ) * 2 = a^2 - a := by 
      have h2' : (a ^ 2 - a) % 2 = 0 := h2 a
      omega
    have eq2 : ((a ^ 2 + a) / 2 : ℕ) ^ 2 = ((a^2 + a) ^ 2) / 4 := by
      have hx : ((a ^ 2 + a) / 2 : ℕ) * 2 = a^2 + a := h3
      have hx2 : ((a ^ 2 + a) / 2) ^ 2 * 4 = ((a ^ 2 + a) ^ 2) := by
        nlinarith [hx, sq_nonneg ((a ^ 2 + a : ℕ) / 2), sq_nonneg (a ^ 2 + a : ℕ)]
      have hx3 : ((a ^ 2 + a) / 2 : ℕ) ^ 2 = ((a^2 + a) ^ 2) / 4 := by
        omega
      exact_mod_cast hx3
    have eq3 : ((a ^ 2 - a) / 2 : ℕ) ^ 2 = ((a^2 - a) ^ 2) / 4 := by
      have hy : ((a ^ 2 - a) / 2 : ℕ) * 2 = a^2 - a := h4
      have hy2 : ((a ^ 2 - a) / 2) ^ 2 * 4 = ((a ^ 2 - a) ^ 2) := by
        nlinarith [hy, sq_nonneg ((a ^ 2 - a : ℕ) / 2), sq_nonneg (a ^ 2 - a : ℕ)]
      have hy3 : ((a ^ 2 - a) / 2 : ℕ) ^ 2 = ((a^2 - a) ^ 2) / 4 := by
        omega
      exact_mod_cast hy3
    rw [eq2, eq3]
    have h5 : (a^2 + a)^2 - (a^2 - a)^2 = 4 * a^3 := by 
      cases a with
      | zero =>
        all_goals
        omega
      | succ n =>
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        <;> ring_nf <;> omega
    have h6 : ((a^2 + a) ^ 2 : ℕ) / 4 - ((a^2 - a) ^ 2) / 4 = a^3 := by
      omega
    exact_mod_cast h6
  linarith [eq1]