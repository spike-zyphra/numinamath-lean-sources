import Mathlib

open Polynomial

/- 10.21. Prove that the polynomial $x^{2 n}+x^{n}+1$ is divisible by $x^{2}+x+1$ if and only if $n$ is not divisible by 3. -/
theorem algebra_225240 {n : ℕ} :
    (X^2 + X + 1 : Polynomial ℝ) ∣ X^(2*n) + X^n + 1 ↔ ¬ 3 ∣ n := by
  -- we'll use strong induction with base case 0, 1, 2
  induction' n using Nat.strong_induction_on with m hm
  match m with
    -- for 0 we have to show X^2+X+1 does not divide 3, we show that by showing degree of X^2+X+1 is 2 while 3's degree is 0
  | 0 =>
    simp
    ring_nf
    by_contra h
    have hd := Polynomial.degree_le_of_dvd h (by norm_num)
    convert_to 2 ≤ degree 3 at hd
    . compute_degree!
    have : degree (3 : ℝ[X]) = 0 := by compute_degree!
    rw [this] at hd
    norm_num at hd
  -- for 1, this is just proving polynomial divides itself
  | 1 =>
    simp
  -- for 2, X^4 + X^2 + 1 = (X^2 + X + 1) * (X^2 - X + 1)
  | 2 =>
    norm_num
    use X^2 - X + 1
    ring
  -- for k + 3, we'll utilize the fact at k
  | k + 3 =>
    specialize hm k (show k < k + 3 by linarith)
    -- in particular 3 ∣ k and 3 ∣ k + 3 are equivalent, so we just have to prove equivalency of X^2 + X + 1 dividing X^(2*k) + X^k + 1 and X^(2*k+6) + X^(k+3) + 1
    rw [Nat.dvd_add_self_right, ← hm]
    -- express X^(2*k+6) + X^(k+3) as sum of X^(2*k) + X^k + 1 and another polynomial
    have hp : (X : ℝ[X]) ^ (2 * (k + 3)) + X ^ (k + 3) + 1
        = (X ^ (2 * k) + X ^ k + 1) + ((X^(2*k + 6) - X^(2*k)) + (X^(k+3) - X^k)) := by
      ring
    rw [hp]
    -- we have to show that X^2 + X + 1 divides the new polynomial
    apply dvd_add_left
    -- we prove divisibliity at two parts individually
    apply dvd_add
    . use X^(2*k) * (X^3 + 1) * (X-1)
      ring
    . use X^k * (X-1)
      ring