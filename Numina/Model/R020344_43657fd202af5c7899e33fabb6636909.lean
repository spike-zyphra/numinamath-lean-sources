import Mathlib

theorem number_theory_130743 {a b A B : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B) (d D : ℕ) (hd : d = Nat.gcd a b)
    (hD : D = Nat.gcd A B) :
    Nat.gcd (Nat.gcd (Nat.gcd (a * A) (a * B)) (b * A)) (b * B) = d * D := by
  rw [hd, hD]
  have h1 : Nat.gcd (a * A) (a * B) = a * (Nat.gcd A B) := by 
    have h2 : Nat.gcd (a * A) (a * B) = a * (Nat.gcd A B) := by 
      rw [Nat.gcd_mul_left]
    exact h2
  calc
    Nat.gcd (Nat.gcd (Nat.gcd (a * A) (a * B)) (b * A)) (b * B) = Nat.gcd (Nat.gcd (a * (Nat.gcd A B)) (b * A)) (b * B) := by 
      rw [h1]
    _ = Nat.gcd (a * (Nat.gcd A B)) (Nat.gcd (b * A) (b * B) ) := by 
      rw [Nat.gcd_assoc]
    _ = Nat.gcd (a * (Nat.gcd A B)) (b * (Nat.gcd A B) ) := by 
      have h2 : Nat.gcd (b * A) (b * B) = b * (Nat.gcd A B) := by 
        rw [Nat.gcd_mul_left]
      rw [h2]
    _ = (Nat.gcd a b) * (Nat.gcd A B) := by 
      have h3 : Nat.gcd (a * (Nat.gcd A B)) (b * (Nat.gcd A B) ) = (Nat.gcd a b) * (Nat.gcd A B) := by 
        rw [Nat.gcd_mul_right]
      rw [h3]