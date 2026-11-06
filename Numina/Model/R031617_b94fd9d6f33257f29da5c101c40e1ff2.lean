import Mathlib

theorem number_theory_128295 (m n : ℕ)
     (hm : 0 < m) 
     (hn : 0 < n) :
    ∃ a b c : ℤ , a * m + b * n = c ∧ (∀ x y : ℕ, 0 < x → 0 < y → a * x + b * y = c) → x = m ∧ y = n := by 
  use 0 
  use 0 
  use 1 
  intro h 
  norm_num at h ⊢ 
  all_goals omega