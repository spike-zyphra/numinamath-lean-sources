import Mathlib

theorem number_theory_75778 (a : ℕ → ℕ) (ha : ∀ k l m n, 0 < a k ∧ 0 < a l ∧ 0 < a m ∧ 0 < a n)
    (h : ∀ k l m n, k * l = m * n → a k + a l = a m + a n) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hdiv : p ∣ q) : a p ≤ a q := by
  have h1 : ∀ l n : ℕ, a l = a n := by 
    intro l n
    have h0 : a 0 + a l = a 0 + a n := by 
      apply h 0 l 0 n 
      all_goals norm_num
    have e1 : a l = a n := by 
      omega 
    exact e1 
  have h2 : a p = a q := by 
    apply h1 p q 
  linarith