import Mathlib

theorem number_theory_140520 (n m : ℕ) (h : 7 ∣ n^2 + m^2) : 49 ∣ n * m := by 
  have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
    omega
  have h2 : m % 7 = 0 ∨ m % 7 = 1 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5 ∨ m % 7 = 6 := by 
    omega
  have h3 : (n ^ 2 + m ^ 2) % 7 = 0 := by
    omega -- from h
  have h4 : n % 7 = 0 := by
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h1, h2] at h3
      <;> omega
    )
  have h5 : m % 7 = 0 := by 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h1, h2] at h3
      <;> omega
    )
  have h6 : 7 ∣ n := by 
    omega
  have h7 : 7 ∣ m := by
    omega
  rcases h6 with ⟨k, hk⟩
  rcases h7 with ⟨l, hl⟩
  have eq1 : n * m = 49 * (k * l) := by
    rw [hk, hl]
    ring
  exact ⟨k * l, by linarith [eq1]⟩