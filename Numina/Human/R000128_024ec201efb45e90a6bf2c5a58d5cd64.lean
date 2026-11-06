import Mathlib

open Finset

/- Divisibility Test 1. If \( d \) divides \( b \) and \( j \) and \( k \) are positive integers with \( j < k \),
then the number represented by \( (a_k \ldots a_1 a_0)_b \) is divisible by \( d^j \) if and only if
the number represented by \( (a_{j-1} \ldots a_1 a_0)_b \) is divisible by \( d^j \).-/
theorem number_theory_4740 {d b j k : ℕ} {a : ℕ → ℕ} (hdb : d ∣ b) (hjk : j < k) :
    d^j ∣ ∑ i ∈ range (k+1), (a i * b ^ i) ↔ d^j ∣ ∑ i ∈ range j, a i * b ^ i := by
  -- Since \( b \equiv 0 \mod d \), Theorem 3.5 informs us that \( b^j \equiv 0 \mod d^j \).
  have hdjbj : d^j ∣ b^j := pow_dvd_pow_of_dvd hdb j
--    Therefore, we can express the number \( (a_k a_{k-1} \ldots a_1 a_0)_b \) as follows:
-- \[
-- \begin{aligned}
-- (a_k a_{k-1} \ldots a_1 a_0)_b & = a_k b^k + a_{k-1} b^{k-1} + \cdots + a_j b^j + a_{j-1} b^{j-1} + \cdots + a_1 b + a_0 \\
-- & \equiv a_{j-1} b^{j-1} + \cdots + a_1 b + a_0 \\
-- & = (a_{j-1} \ldots a_1 a_0)_b \mod d^j
-- \end{aligned}
-- \]
  have hajk : ∑ i ∈ range (k+1), (a i * b ^ i) = ∑ i ∈ range j, (a i * b ^ i) +
      ∑ i ∈ Ico j (k+1), (a i * b ^ i) :=
    Eq.symm <| sum_range_add_sum_Ico (fun k => a k * b ^ k) (by linarith)
  have hdjajk : d^j ∣ ∑ i ∈ Ico j (k+1), (a i * b ^ i) := by
      refine dvd_sum fun i hi => dvd_mul_of_dvd_right (hdjbj.trans ?_) _
      apply Nat.pow_dvd_pow; simp at hi; exact hi.1
  rw [hajk, Iff.comm]
  exact Nat.dvd_add_iff_left hdjajk
