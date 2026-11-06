import Mathlib

theorem number_theory_4834 {x : ℕ} :
    (x=2821 → x.primeFactorsList = [7,13,31] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=10585 → x.primeFactorsList = [5,29,73] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=29341 → x.primeFactorsList = [13,37,61] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=314821 → x.primeFactorsList = [13,61,397] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=172081 → x.primeFactorsList = [7,13,31,61] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=564651361 → x.primeFactorsList = [43,3361,3907] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) := by
  split_ands
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      norm_num
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      norm_num
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      norm_num
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      norm_num
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals
      norm_num
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      norm_num