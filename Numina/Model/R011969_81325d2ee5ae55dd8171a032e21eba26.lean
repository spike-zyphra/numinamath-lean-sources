import Mathlib

def a : ℕ → ℤ
| 0 => 0
| 1 => 2
| n + 2 => 2 * a (n + 1) + 41 * a n

theorem number_theory_84778 : 2017 ∣ a 2016 := by 
  have h1 : ∀ n : ℕ, 2017 ∣ a (8 * n) := by
    intro n
    induction n with
    | zero => 
      norm_num [a]
    | succ n ih =>
      norm_num [a, mul_add, add_mul] at ih ⊢ 
      all_goals 
        omega

  have h2 : 2017 ∣ a 2016 := by 
    have h3 : 2017 ∣ a (8 * 252) := h1 252 
    norm_num at h3 ⊢ 
    all_goals omega 
  exact h2