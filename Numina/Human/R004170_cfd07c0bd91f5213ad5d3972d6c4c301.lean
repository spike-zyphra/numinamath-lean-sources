import Mathlib

/-
Example 6 (1987 Canadian Mathematics Competition) 1987 can be written as a three-digit number $\overline{x y z}$ in base $b$, if $x+y+z=1+9+8+7$, try to determine all possible $x, y, z$ and $b$.
-/

theorem number_theory_240680 (n b x y z : ℕ) (hn: n = 1987) : 
(Nat.digits b n = [z,y,x])∧(x+y+z = 1 + 9 + 8 + 7)
↔
b = 19 ∧ x= 5 ∧ y = 9 ∧ z = 11 := by 

  simp

  constructor
  
  --From left to right.
  intro ⟨h1,h2⟩

  --The leading term is non-zero.
  have xpos : 1 ≤ x := by 
    have : x ≠ 0 := by 
      have : (b.digits n).getLast (by simp [h1]) ≠ 0 := by 
        apply Nat.getLast_digit_ne_zero
        simp [hn]
      simp [h1] at this
      simp [this]
    omega

  --b is larger than 10, since 1987 has four digits in base 10, more than 3.
  have bg10 : 10 < b := by
    by_contra ble10
    push_neg at ble10
    have : (b.digits n).length = 3 := by
      simp [h1]
    have t: n < b ^ (b.digits n).length := by
      apply Nat.lt_base_pow_length_digits
      by_contra nle1
      push_neg at nle1
      by_cases be1 : b = 1 
      rw [hn, be1] at h1
      rw [Nat.digits_one] at h1
      have l1 : (List.replicate 1987 1).length = 1987 := by 
        apply List.length_replicate
      have l2 : [z,y,x].length = 3 := by simp
      have l3 : (List.replicate 1987 1).length = [z,y,x].length := by rw [h1]
      linarith
      have be0 : b = 0 := by omega
      simp [hn,be0] at h1
    rw [this] at t
    rw [hn] at t
    have : b^3 ≤ 10^3 := by exact Nat.pow_le_pow_of_le_left ble10 3
    linarith

  --We rewrite our equation and get that (b-1) ∣ 1962 and b-1 ≤ 50.
  have eq : x*b^2 + y*b + z = n := by 
    rw [← Nat.ofDigits_digits b n]
    rw [h1]
    have : Nat.ofDigits b [z, y, x] = z + b * Nat.ofDigits b [y, x] := by exact rfl
    rw [this]
    have : Nat.ofDigits b [y, x] = y + b * x := by exact rfl
    rw [this]
    ring
  have eq2 : (b-1)*((b+1)*x+y) = 1962 := by 
    have : (b-1)*((b+1)*x+y) + (x+y+z) = (x*b^2 + y*b + z)  := by 
      ring_nf
      zify
      have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (b - 1) = b-1 := by omega
      rw [this]
      ring
    simp [eq, h2, hn] at this
    exact this

  have ub : b - 1 ≤ 50 := by 
    by_contra gg
    have : b - 1 ≤ ((b+1)*x+y) := by nlinarith
    have : 50*50 ≤ (b-1)*((b+1)*x+y) := by nlinarith
    simp [eq2] at this

  --Then we check the divisors of 1962 and get that b = 19. Then x = 5, y = 9, z = 11.
  have dd : (b-1) ∣ 1962 := by use ((b+1)*x+y); linarith
  have nd1962 : Nat.divisors 1962 = {1,2,3,6,9,18,109,218,327,654,981,1962} := by native_decide
  have dd' : (b-1) ∈ Nat.divisors 1962 := by 
    rw [Nat.mem_divisors]
    simp [dd]
  rw [nd1962] at dd'
  simp at dd'
  rcases dd' with de | de | de | de | de | de | de | de | de | de | de | de <;>
  simp [de] at bg10 ub h1 ⊢
  simp [hn] at h1
  omega
  
  

  --From right to left, simple verifications.
  intro ⟨be,xe,ye,ze⟩
  simp [hn,be,xe,ye,ze]