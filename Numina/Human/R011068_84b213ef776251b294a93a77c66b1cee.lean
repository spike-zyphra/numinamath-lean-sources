import Mathlib

open Nat

/- Problem: Given $a < b$, and both $a$ and $b$ are prime numbers, $n$ is an odd number.
   $a$, $b$, $n$ satisfy the equation $a + bn = 487$. Find the values of $a$, $b$, and $n$. -/
theorem algebra_9222 {a b n : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a < b)
    (hn : Odd n) (h1 : a + b * n = 487) :
    (a = 2 ∧ b = 97 ∧ n = 5) ∨ (a = 2 ∧ b = 5 ∧ n = 97) := by
  -- Since b > a and a is prime, b must be greater than 2
  have hb_gt : 2 < b := lt_of_le_of_lt (Nat.Prime.two_le ha) h
  -- Therefore b is odd (as it's a prime > 2)
  have hb_odd := Nat.Prime.odd_of_ne_two hb (Nat.ne_of_gt hb_gt)
  -- Product of odd numbers b and n is odd
  have hnb_odd := (Nat.odd_mul).mpr ⟨hb_odd, hn⟩
  -- It is easy to show that 487 is odd
  have h487_odd : Odd 487 := by decide
  rw [add_comm] at h1
  rw [← h1] at h487_odd
  -- Since b*n and 487 are odd, a must be even
  have ha_even : Even a := ((Nat.odd_add).mp h487_odd).mp hnb_odd
  -- Since a is prime and even, a must be 2
  have ha_eq_2 : a = 2 := (Nat.Prime.even_iff ha).mp ha_even
  -- Therefore b*n = 485
  have hbn_eq_485 : b * n = 485 := by linarith
  -- 485 has prime factors 5 and 97
  have h485_primeFactors : Nat.primeFactors 485 = {5, 97} := by native_decide
  -- b must be a factor of 485
  have : b ∣ 485 := by
    rw [← hbn_eq_485]
    exact dvd_mul_right b n
  -- Therefore b must be one of the prime factors of 485
  have hb_mem_primeFactors : b ∈ Nat.primeFactors 485 :=
    Nat.mem_primeFactors.mpr ⟨hb, this, (by decide)⟩
  -- Since b must be either 5 or 97, we consider both cases
  rw [h485_primeFactors] at hb_mem_primeFactors
  simp at hb_mem_primeFactors
  match hb_mem_primeFactors with
  | Or.inl h5 =>  -- Case b = 5
    rw [h5, (show 485 = 5 * 97 by decide)] at hbn_eq_485
    exact Or.inr <|  ⟨ha_eq_2, h5 , Nat.mul_left_cancel (by decide) hbn_eq_485⟩
  | Or.inr h97 =>  -- Case b = 97
    rw [h97, (show 485 = 97 * 5 by decide)] at hbn_eq_485
    exact Or.inl <|  ⟨ha_eq_2, h97 , Nat.mul_left_cancel (by decide) hbn_eq_485⟩
