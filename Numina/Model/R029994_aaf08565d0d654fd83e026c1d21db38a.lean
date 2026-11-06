import Mathlib

theorem number_theory_197884 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : a * 1 + (a - 10) * 2 = 55) (h2 : Nat.lcm a b = 280) (h3 : Nat.gcd a b = 10) :
    b = 40 := by
  have ha25 : a = 25 := by 
    omega
  -- substitute a = 25 into h2 and h3
  rw [ha25] at h2 h3 
  -- apply the relationship between gcd and lcm
  have h4 : Nat.gcd 25 b * Nat.lcm 25 b = 25 * b := by 
    rw [Nat.gcd_mul_lcm]
  -- substitute the given conditions into the equation
  rw [h2, h3] at h4
  -- this implies `10 * 280 = 25 * b` which simplifies to `2800 = 25 * b`, hence `b = 112`.
  have h5 : 10 * 280 = 25 * b := by 
    linarith 
  have h6 : b = 112 := by
    omega 
  -- if b = 112, check the gcd is 10 or not, but it's actually 1.
  rw [h6] at h3 
  norm_num at h3 
  all_goals omega