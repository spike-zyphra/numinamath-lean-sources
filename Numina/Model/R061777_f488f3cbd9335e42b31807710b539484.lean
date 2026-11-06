import Mathlib

theorem number_theory_5914 {a b c d e f : ℤ} (ha : a = 15) (hb : b = 21) (hc : c = -35)
    (hd : d = 210) (he : e = -330) (hf : f = 1155) :
    Int.gcd (Int.gcd a b) c = 1 ∧ 1 = 36 * a - 24 * b + c ∧
    Int.gcd (Int.gcd d e) f = 15 ∧ 15 = 114 * d + 76 * e + f := by
  rw [ha, hb, hc, hd, he, hf]
  constructor
  · -- First, compute gcd(gcd(15, 21), -35) = 1
    norm_num [Int.gcd]
  constructor
  · -- Verify that 1 = 36 * 15 - 24 * 21 + (-35)
    norm_num
  constructor
  · -- Further compute gcd(gcd(210, -330), 1155) = 15
    norm_num [Int.gcd]
  · -- Finally verify that 15 = 114 * 210 + 76 * (-330) + 1155
    norm_num