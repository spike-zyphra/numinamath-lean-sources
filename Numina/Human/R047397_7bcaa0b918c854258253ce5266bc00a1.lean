import Mathlib

/- If \( c \) and \( d \) are integers and \( c = dq + r \) where \( c \) and \( d \) are integers, then the greatest common divisor of \( c \) and \( d \) is equal to the greatest common divisor of \( d \) and \( r \), that is, \( (c, d) = (d, r) \).-/
theorem number_theory_4529 (c q r d : ℤ) (h₀ : c = d * q + r) :
    Int.gcd c d = Int.gcd d r := by
  -- prove equality by antisymm of dvd
  apply Nat.dvd_antisymm
  -- prove that gcd(c,d) | gcd(d,r)
  apply Nat.dvd_gcd
  . apply Nat.gcd_dvd_right
  . have : (Int.gcd c d : ℤ) ∣ c := Int.gcd_dvd_left
    -- as c=dq+r we can conclude that gcd(c,d) | r
    conv_rhs at this => rw [h₀]
    rwa [Int.dvd_add_right, Int.ofNat_dvd_left] at this
    . apply Dvd.dvd.mul_right
      exact Int.gcd_dvd_right
  -- prove that gcd(d,r) | gcd(c,d)
  apply Nat.dvd_gcd
  . rw [← Int.ofNat_dvd_left, h₀]
    -- by definition of `gcd` we can deduce gcd(d,r) | dq+r
    apply Int.dvd_add
    . apply Dvd.dvd.mul_right
      apply Int.gcd_dvd_left
    . apply Int.gcd_dvd_right
  . apply Nat.gcd_dvd_left
