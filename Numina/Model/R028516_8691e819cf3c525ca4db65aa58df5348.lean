import Mathlib

def d : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_1150 :
    ¬∃ n, 0 < n ∧ d (d (d (d (d n)))) + d (d (d (d n))) + d (d (d n)) + d (d n) + d n + n = 2015249 := by
  rintro ⟨n, hn1, hn2⟩
  have h_mod9 : ∀ n : ℕ, d n % 9 = n % 9 := by 
    intro n 
    have h1 : d n = (Nat.digits 10 n).sum := rfl 
    rw [h1]
    have h2 : (Nat.digits 10 n).sum % 9 = n % 9 := by 
      have h3 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
        rw [Nat.modEq_nine_digits_sum (n)]
        all_goals omega 
      omega 
    omega 
  have h3 : (d (d (d (d (d n)))) + d (d (d (d n))) + d (d (d n)) + d (d n) + d n + n) % 9 = 2015249 % 9 := by 
    omega 
  have h4 : (d (d (d (d (d n)))) + d (d (d (d n))) + d (d (d n)) + d (d n) + d n + n) % 9 = (6 * n) % 9 := by
    simp [Nat.add_mod, h_mod9]
    all_goals omega 
  have h5 : (2015249 : ℕ) % 9 = 5 := by norm_num 
  rw [h4] at h3 
  rw [h5] at h3 
  omega