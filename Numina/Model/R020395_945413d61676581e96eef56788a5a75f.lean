import Mathlib

theorem number_theory_283161 :
    IsGreatest {x | ∀ y, x ∣ 7^y + 12 * y - 1} 18 := by
  constructor
  · -- Show 18 is in the set
    show ∀ y, 18 ∣ 7 ^ y + 12 * y - 1
    intro y
    induction y with
    | zero =>
      norm_num
    | succ y ih =>
      cases y with
      | zero =>
        norm_num at ih ⊢
      | succ y =>
        simp [pow_succ, pow_zero, Nat.mul_add, Nat.add_mul] at ih ⊢
        ring_nf at ih ⊢
        all_goals omega
  · -- Show it is greatest
    intro x hx
    have h1 := hx 1
    norm_num at h1
    have h2 : x ∣ 18 := by 
      exact h1
    have h3 : x ≤ 18 := by
      exact Nat.le_of_dvd (by norm_num) h2
    linarith