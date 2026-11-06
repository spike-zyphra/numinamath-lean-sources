import Mathlib

theorem number_theory_16434 (IsComposite : ℕ → Prop)
    (isComposite_def : ∀ n, IsComposite n ↔ 2 ≤ n ∧ ¬n.Prime) :
    IsGreatest {n : ℕ | IsComposite n ∧ ∀ x : ℕ, n ∣ x ^ 3 - x} 6 := by
  constructor
  · -- Show 6 is in the set
    constructor
    · -- Show 6 is composite
      rw [isComposite_def]
      constructor
      · norm_num
      · norm_num
    · -- Show that for all x, 6 divides x^3 - x
      intro x
      have h1 : x ^ 3 % 6 = x % 6 := by
        have h1 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by 
          omega
        rcases h1 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
      have h2 : (x ^ 3 - x) % 6 = 0 := by
        omega
      have h3 : 6 ∣ x ^ 3 - x := by 
        omega
      exact h3
  · -- Show that 6 is greatest in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    rw [isComposite_def] at h1
    rcases h1 with ⟨h1, h1_not_prime⟩
    have h3 : n ∣ 2 ^ 3 - 2 := by 
      apply h2 2
    have h4 : n ∣ 6 := by 
      norm_num at h3 ⊢
      exact h3
    have h5 : n ≤ 6 := by 
      exact Nat.le_of_dvd (by norm_num) h4
    linarith