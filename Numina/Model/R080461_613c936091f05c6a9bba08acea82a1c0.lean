import Mathlib

theorem number_theory_19604 : 2 * n ≡ 15 [MOD 47] ↔ n ≡ 31 [MOD 47] := by 
  simp only [Nat.ModEq]
  constructor
  · intro h
    -- Given 2n ≡ 15 (mod 47), prove n ≡ 31 (mod 47)
    -- From 2n ≡ 15 (mod 47), we have that 2n % 47 = 15
    -- This is equivalent to 2n = 47k + 15 for some integer k
    -- From here, n must be unique mod 47, and we can check that n ≡ 31 works
    -- The equation 2n ≡ 15 (mod 47) is equivalent to n ≡ 31 (mod 47)
    -- Multiply both sides by the inverse of 2 mod 47, which is 24
    -- So n ≡ 15 * 24 (mod 47)
    -- Compute 15 * 24 = 360
    -- Then 360 ≡ 31 (mod 47)
    -- So n ≡ 31 (mod 47)
    -- Now we need to express this as an equation plus a divisibility condition
    -- 47 ∣ (n - 31)
    omega
  · intro h
    -- Assume n ≡ 31 (mod 47), prove 2n ≡ 15 (mod 47)
    -- Now n % 47 = 31, so n ≡ 31 (mod 47)
    -- Multiply both sides by 2: 2n ≡ 62 (mod 47)
    -- 62 ≡ 15 (mod 47) as required
    -- To formalize this, we need to set up the divisibility condition
    -- 47 ∣ (2n - 15)
    omega