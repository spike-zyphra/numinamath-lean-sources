import Mathlib

theorem number_theory_130118 (a: ℕ → ℕ) (ha0: a 0 = 3) (h: ∀ n, a (n+1) = (a n)^2):
(a 2006)%10 = 1 := by
have ha1 : a 1 = 9 := by simp [ha0, h]
have ha2 : a 2 = 81 := by simp [ha1, h]
have h1 : ∀ n : ℕ, a (n + 2) % 10 = 1 := by
  intro n 
  induction n with
  | zero =>
    norm_num [ha2]
  | succ n hn =>
    have eq1 : a (n + 3) = (a (n + 2)) ^ 2 := by 
      specialize h (n + 2)
      simpa using h 
    rw [eq1] at *
    have eq3 : a (n + 2) % 10 = 1 := by 
      simpa using hn 
    have eq5 : (a (n + 2) ) ^ 2 % 10 = 1 := by
      have h1 : a (n + 2) % 10 = 1 := eq3
      have h2 : (a (n + 2) ) ^ 2 % 10 = (1) ^ 2 % 10 := by
        simp [Nat.pow_mod, h1]
        <;> omega 
      norm_num at h2 ⊢
      <;> omega 
    omega
have eq4 : 2006 = 2004 + 2 := by
  omega
rw [eq4]
apply h1