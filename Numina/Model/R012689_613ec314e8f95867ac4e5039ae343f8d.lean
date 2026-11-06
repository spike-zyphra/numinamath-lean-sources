import Mathlib

def f : ℕ → ℕ
| 0 => 1
| 1 => 3
| n + 2 => 2 * (f n + f (n + 1))

theorem number_theory_203127 : f 1999 % 9 = 3 := by
  have h1 : ∀ (n : ℕ), f (9 * n + 1) % 9 = 3 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [f]
    | succ n ih =>
      simp [f, Nat.add_assoc] at ih ⊢ 
      <;> ring_nf at ih ⊢
      all_goals 
        omega
  have h2 : (9 * (222 : ℕ) + 1 : ℕ) = 1999 := by 
    omega
  have h3 : f 1999 % 9 = 3 := by 
    have h4 : f (9 * (222 : ℕ) + 1) % 9 = 3 := h1 222 
    rw [h2] at h4 
    exact h4 
  exact h3