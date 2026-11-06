import Mathlib

open Finset

/- Divisibility Test 2. If \( d \) divides \( (b-1) \),
then a number \( n = (a_k \ldots a_1 a_0)_b \) is divisible by \( d \) if and only if
 the sum of its digits \( a_k + a_{k-1} + \cdots + a_1 + a_0 \) is divisible by \( d \).-/
theorem number_theory_4741 {k : ℕ} {d b : ℤ} {a : ℕ → ℤ} (hdb : d ∣ (b-1)):
    d ∣ ∑ i ∈ range (k+1), a i * b ^ i ↔ d ∣ ∑ i ∈ range (k+1), a i := by
--    Proof. Since \( d \) divides \( (b-1) \), we have \( b \equiv 1 \pmod{d} \). This means that when we raise \( b \) to any positive integer power, it will also be congruent to 1 modulo \( d \). Specifically, by Theorem 3.5, we know that \( b^j \equiv 1 \pmod{d} \) for all positive integers \( j \).
-- Now, we can express the number \( n \) in base \( b \) as follows:
-- \[
-- n = (a_k \ldots a_1 a_0)_b = a_k b^k + a_{k-1} b^{k-1} + \cdots + a_1 b + a_0.
-- \]
-- Using the congruence \( b^j \equiv 1 \pmod{d} \), we can replace each power of \( b \) in the expression for \( n \):
-- \[
-- n \equiv a_k \cdot 1 + a_{k-1} \cdot 1 + \cdots + a_1 \cdot 1 + a_0 \pmod{d}.
-- \]
-- This simplifies to:
-- \[
-- n \equiv a_k + a_{k-1} + \cdots + a_1 + a_0 \pmod{d}.
-- \]
-- Thus, we conclude that \( d \) divides \( n \) if and only if \( d \) divides the sum of its digits \( a_k + a_{k-1} + \cdots + a_1 + a_0 \). This completes the proof.
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero]
  conv => congr; rw [sum_int_mod]; rfl; rw [sum_int_mod]
  suffices ∑ i ∈ range (k+1), a i * b ^ i % d = ∑ i ∈ range (k+1), a i % d by rw [this]
  refine sum_congr rfl fun i _ => ?_
  suffices b^i ≡ 1 [ZMOD d] by
    nth_rw 2 [← mul_one (a i)]
    apply Int.ModEq.mul_left
    assumption
  rw [← one_pow i]
  apply Int.ModEq.pow
  rwa [Int.modEq_iff_dvd, dvd_sub_comm]
