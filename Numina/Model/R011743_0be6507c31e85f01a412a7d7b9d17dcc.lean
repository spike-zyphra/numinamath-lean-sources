import Mathlib

theorem number_theory_283854 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hsum : x + y = 432) (hlcm : Nat.lcm x y + Nat.gcd x y = 7776) :
    x * y = 46620 := by
  have h1 : x * y = Nat.gcd x y * Nat.lcm x y := by
    rw [Nat.gcd_mul_lcm]
  have h2 : Nat.lcm x y = 7776 - Nat.gcd x y := by
    omega
  have h3 : x * y = Nat.gcd x y * (7776 - Nat.gcd x y) := by 
    rw [h2] at h1
    linarith
  have h4 : x ≤ 432 := by omega
  have h5 : y = 432 - x := by omega
  interval_cases x <;> norm_num [Nat.lcm, Nat.gcd, h5] at h3 hlcm h1 ⊢
  <;> omega