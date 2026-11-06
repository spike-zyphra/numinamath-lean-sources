import Mathlib

open Finset

/- Divisibility Test 3. If \( d \) divides \( (b+1) \),
then a number \( n = (a_k \ldots a_1 a_0)_b \) is divisible by \( d \) if and only if
the expression \( (-1)^k a_k + \cdots - a_1 + a_0 \) is divisible by \( d \).-/
theorem number_theory_4742 {k : ℕ} {d b : ℤ} {a : ℕ → ℤ} (hdb : d ∣ (b+1)):
    d ∣ ∑ i ∈ range (k+1), (a i * b ^ i) ↔ d ∣ ∑ i ∈ range (k+1), (-1)^i * a i := by
--    Proof. Since \( d \) divides \( (b+1) \), we can express this as \( b \equiv -1 \pmod{d} \). This means that for any integer \( j \), we have \( b^j \equiv (-1)^j \pmod{d} \).

-- Now, we can express the number \( n \) in base \( b \) as follows:
-- \[
-- n = a_k b^k + a_{k-1} b^{k-1} + \cdots + a_1 b + a_0.
-- \]
-- Substituting the congruence \( b \equiv -1 \pmod{d} \) into the expression for \( n \), we get:
-- \[
-- n \equiv a_k (-1)^k + a_{k-1} (-1)^{k-1} + \cdots + a_1 (-1) + a_0 \pmod{d}.
-- \]
-- This simplifies to:
-- \[
-- n \equiv (-1)^k a_k + (-1)^{k-1} a_{k-1} + \cdots - a_1 + a_0 \pmod{d}.
-- \]
-- Thus, \( n \) is divisible by \( d \) if and only if the sum \( (-1)^k a_k + (-1)^{k-1} a_{k-1} + \cdots - a_1 + a_0 \) is divisible by \( d \).

-- Therefore, we conclude that \( d \mid n \) if and only if \( d \mid \left((-1)^k a_k + \cdots - a_1 + a_0\right) \).
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero]
  conv => congr; rw [sum_int_mod]; rfl; rw [sum_int_mod]
  suffices ∑ i ∈ range (k+1), a i * b ^ i % d = ∑ i ∈ range (k+1), (-1)^i * a i % d by rw [this]
  refine sum_congr rfl fun i _ => ?_
  suffices b^i ≡ (-1)^i [ZMOD d] by
    rw [mul_comm]
    apply Int.ModEq.mul_right
    assumption
  apply Int.ModEq.pow
  rwa [Int.modEq_iff_dvd, dvd_sub_comm]
