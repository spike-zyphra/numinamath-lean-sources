import Mathlib

theorem number_theory_51156 (a : ℕ → ℕ) (ha : StrictMono a)
    (h : ∀ n > 100, IsLeast {x | x > a (n - 1) ∧ ∀ i ∈ Finset.Icc 1 (n - 1), ¬(x % i = 0)} (a n)) :
    Set.Finite {n | ¬Nat.Prime (a n)} := by 
  have h_false : False := by 
    have h1 := h 101 (by norm_num)
    have h5 : a 101 ∈ {x | x > a 100 ∧ ∀ i ∈ Finset.Icc 1 100, ¬(x % i = 0)} := by
      have h6 : IsLeast {x | x > a 100 ∧ ∀ i ∈ Finset.Icc 1 100, ¬(x % i = 0)} (a 101) := h1
      have h7 : a 101 ∈ {x | x > a 100 ∧ ∀ i ∈ Finset.Icc 1 100, ¬(x % i = 0)} := by 
        exact h6.left
      exact h7
    have h6_cond : ∀ i ∈ Finset.Icc 1 100, ¬(a 101 % i = 0) := by 
      simpa using h5.right
    have h3 : (1 : ℕ) ∈ Finset.Icc 1 100 := by 
      norm_num
    have h7 : ¬(a 101 % 1 = 0) := h6_cond 1 h3
    have h8 : a 101 % 1 = 0 := by 
      omega
    contradiction 
  contradiction