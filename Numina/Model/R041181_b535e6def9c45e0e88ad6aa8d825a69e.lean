import Mathlib

open Nat

theorem number_theory_136392 {a b a' b' d d' : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hd : d = Nat.gcd a b) (hd' : d' = Nat.gcd a' b')
    (h : a = a' * d) (h' : b = b' * d') :
    Nat.gcd (a * a') (Nat.gcd (a * b') (Nat.gcd (b * a') (b * b'))) = d * d' := by
  rw [h, h']
  have h1 : Nat.gcd (a' * d * a') (a' * d * b') = a' * d * d' := by
    rw [show a' * d * a' = (a' * d) * a' by ring, show a' * d * b' = (a' * d) * b' by ring]
    rw [Nat.gcd_mul_left]
    rw [show d' = Nat.gcd a' b' by rw [hd']]
  have h2 : Nat.gcd (b' * d' * a') (b' * d' * b') = b' * d' * d' := by
    rw [show b' * d' * a' = (b' * d') * a' by ring, show b' * d' * b' = (b' * d') * b' by ring]
    rw [Nat.gcd_mul_left]
    rw [show d' = Nat.gcd a' b' by rw [hd']]
  have h3 : Nat.gcd (a' * d * a') (Nat.gcd (a' * d * b') (Nat.gcd (b' * d' * a') (b' * d' * b'))) = Nat.gcd (a' * d * a') (Nat.gcd (a' * d * b') (b' * d' * d')) := by
    rw [h2]
  rw [h3]
  have h4 : Nat.gcd (a' * d * a') (Nat.gcd (a' * d * b') (b' * d' * d')) = Nat.gcd (Nat.gcd (a' * d * a') (a' * d * b')) (b' * d' * d') := by
    rw [← Nat.gcd_assoc]
  rw [h4, h1]
  have h5 : Nat.gcd (a' * d * d') (b' * d' * d') = d' * (Nat.gcd (a' * d) (b' * d')) := by
    rw [show a' * d * d' = (d') * (a' * d) by ring, show b' * d' * d' = (d') * (b' * d') by ring]
    rw [Nat.gcd_mul_left]
  rw [h5]
  have h7 : Nat.gcd (a' * d) (b' * d') = d := by
    have h8 : a' * d = a := by
      omega
    have h9 : b' * d' = b := by
      omega
    rw [h8, h9, hd]
  rw [h7]
  all_goals ring