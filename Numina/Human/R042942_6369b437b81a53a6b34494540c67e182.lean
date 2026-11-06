import Mathlib

/- In the base-three number system, $a = 2012_3$ and $b = 201_3.$ What is the product $ab$ expressed in the base-three number system? -/
theorem number_theory_18638 {a b : ℕ}
    (ha: Nat.digits 3 a = [2,1,0,2])
    (hb: Nat.digits 3 b = [1,0,2]):
    Nat.digits 3 (a * b) = [2, 1, 1, 2, 1, 1, 1] := by
  -- a = 2x3^3+1x3+2 = 59
  have h1: a = 59 := by
    rw [← Nat.ofDigits_digits 3 a, ha]
    repeat' rw [Nat.ofDigits]; simp
  -- b = 2x3^2+1 = 19
  have h2: b = 19 := by
    rw [← Nat.ofDigits_digits 3 b, hb]
    repeat' rw [Nat.ofDigits]; simp
  -- so ab = 59x19 = 1121
  have h3: a*b = 1121 := by
    rw [h1, h2]
  -- and 1121(base10) in base 3 is 1112112
  have h4: Nat.digits 3 1121 = [2,1,1,2,1,1,1] := by
    norm_num
  -- so ab = 1112112 (base 3)
  rw [h3, h4]