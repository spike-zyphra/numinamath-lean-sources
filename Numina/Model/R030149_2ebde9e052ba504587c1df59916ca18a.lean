import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 => f (n + 2) + f (n + 1)

theorem number_theory_121786 (k : ℕ) : 5 ∣ f (5 * k) := by 
  have h1 : ∀ (k : ℕ), f (5 * k) % 5 = 0 := by 
    intro k
    induction k with 
    | zero =>
      simp [f]
    | succ k ih1 =>
      have h1' : f (5 * (k + 1)) % 5 = 0 := by
        have h11 : f (5 * k) % 5 = 0 := by 
          exact ih1
        have h12 : f (5 * (k + 1)) = f (5 * k + 5) := by
          ring_nf 
        rw [h12]
        -- Show that f (5 * k + 5) % 5 = 0 using the hypothesis
        have h2 : ∀ (k : ℕ), f (5 * k + 5) % 5 = 0 := by
          intro k 
          induction k with 
          | zero =>
            simp [f]
            <;> omega
          | succ k ih2 =>
            simp [f] at ih2 ⊢ 
            <;> ring_nf at ih2 ⊢ 
            <;> omega 
        specialize h2 k 
        exact h2 
      exact h1'
  have h2 : f (5 * k) % 5 = 0 := h1 k 
  exact Nat.dvd_of_mod_eq_zero h2