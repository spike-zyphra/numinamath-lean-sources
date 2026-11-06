import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_111318 (n : ℕ) (h₀ : n ≠ 0) :
    S n = S (2 * n) → 9 ∣ n := by 
  intro h_eq
  have h1 : n % 9 = S n % 9 := by
    have h2 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
      exact Nat.modEq_nine_digits_sum (n)
    have h3 : S n = (Nat.digits 10 n).sum := by 
      rfl 
    simp [h3] at *
    all_goals 
      omega 
  have h2 : (2 * n) % 9 = S (2 * n) % 9 := by 
    have eq1 : (2 * n) % 9 = ((Nat.digits 10 (2 * n)).sum) % 9 := by
      exact Nat.modEq_nine_digits_sum (2 * n)
    have eq2 : S (2 * n) = (Nat.digits 10 (2 * n)).sum := by
      rfl 
    have eq3 : (2 * n) % 9 = S (2 * n) % 9 := by 
      rw [show S (2 * n) = (Nat.digits 10 (2 * n)).sum by rfl] 
      omega -- This uses eq1
    exact_mod_cast eq3 
  have h3 : S n = S (2 * n) := h_eq
  have h4 : n % 9 = (2 * n) % 9 := by 
    omega 
  have h5 : 9 ∣ n := by
    omega 
  exact h5