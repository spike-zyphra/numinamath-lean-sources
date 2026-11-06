import Mathlib

theorem number_theory_15799 (m : ℕ) (h : m ≠ 0) (h1 : (Nat.divisors (Nat.gcd 90 m)).card = 3) :
    (Nat.divisors (Nat.gcd 90 m)).max = 9 := by 
  have h4 : Nat.gcd 90 m ∣ 90 := by
    apply Nat.gcd_dvd_left
  have h5 : Nat.gcd 90 m ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.gcd_pos_of_pos_left
    omega
  have h8 : Nat.gcd 90 m ≤ 90 := by
    exact Nat.le_of_dvd (by omega) h4
  interval_cases g : Nat.gcd 90 m <;> norm_num at h1 h4 h5 ⊢
  <;> try { all_goals tauto }