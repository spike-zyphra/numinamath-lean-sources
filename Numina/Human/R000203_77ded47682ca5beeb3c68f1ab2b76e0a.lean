import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-Let  $p$  be a prime and  $n$  be a positive integer such that  $p^2$  divides  $\prod_{k=1}^n (k^2+1)$ . Show that  $p<2n$ .-/
theorem number_theory_8550 (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n)
(hsq : p^2 ∣ ∏ k in Finset.Icc 1 n, (k^2 + 1)) :
p < 2 * n := by
-- Write out the definition of prime numbers
  rcases Nat.prime_def_lt.mp hp with ⟨hpl,_⟩
-- Use induction on $n$
  induction n with
-- Case $n=0$
  | zero => linarith
-- Assume case $n$ and prove case $n+1$
  | succ n ih =>
-- Show that $n$ is not $0$
    by_cases h' : n = 0
    · rw [h']; simp; rw [h'] at hsq; simp at hsq
      have h'p : 4 ≤ p^2 := by
        rw [show 4=2^2 by norm_num, Nat.pow_le_pow_iff_left]
        assumption; norm_num
      have := Nat.le_of_dvd (show 0<2 by norm_num) hsq
      linarith
-- Rewrite assumptions
    push_neg at h'; apply Nat.pos_iff_ne_zero.mpr at h'
    replace ih := ih h'
-- Prove by the cases that $p^2$ divides the product or not
    by_cases h'' : p ^ 2 ∣ ∏ k ∈ Finset.Icc 1 n, (k ^ 2 + 1)
    · replace ih := ih h''; linarith
-- Simplify notations
    let a := ∏ k ∈ Finset.Icc 1 n, (k ^ 2 + 1)
    replace h'' : ¬p ^ 2 ∣ a := by simp [a]; assumption
-- Split the product indexed from $1$ to $n+1$ as the product of the product indexed from $1$ to $n$ and the $n+1$-th term
    have r1 : ∏ k ∈ Finset.Icc 1 (n + 1), (k ^ 2 + 1) = a * ((n + 1) ^ 2 + 1) := by
      apply Finset.prod_Icc_succ_top; simp
-- Since $p^2$ divides the product, we can split this fact to a few cases
    rw [r1, Nat.dvd_mul] at hsq
    rcases hsq with ⟨y, z, hsq1, hsq2, hsq3⟩
    have r2 : y ∣ p ^ 2 := by use z; symm; assumption
    rw [Nat.dvd_prime_pow] at r2
    rcases r2 with ⟨k, hk1, hk2⟩
    cases hk1 with
-- Case $p^2$ divides $a$
    | refl => rw [hk2] at hsq1; contradiction
    | step h'k =>
      simp at h'k; cases h'k with
-- Case $p$ divides $a$
      | refl =>
        simp at hk2; rw [hk2, pow_two] at hsq3; rw [hk2] at hsq1
        simp at hsq3; rcases hsq3 with hsq3l | hsq3r
        · rw [hsq3l] at hsq2; simp [a] at hsq1
-- $p$ divides the product means $p$ divides one of the factors since $p$ is prime
          rw [Prime.dvd_finset_prod_iff] at hsq1
          rcases hsq1 with ⟨i, hi1, hi2⟩; simp at hi1
          rcases hi1 with ⟨hi1l,hi1r⟩
          have t1 : i ^ 2 + 1 ≤ (n + 1) ^ 2 + 1 := by
            have : i < n+1 := by linarith
            simp; rw [Nat.pow_le_pow_iff_left]; linarith; norm_num
-- Since $p$ divides both $(n+1)^2+1$ and $i^2+1$, it divides their difference
          have t2 := Nat.dvd_sub t1 hsq2 hi2
          have t3 : (n + 1) ^ 2 + 1 - (i ^ 2 + 1) = (n + 1 + i) * (n + 1 - i) := by
            rw [Nat.add_sub_add_right, sq_sub_sq]
-- The difference is again a product, so $p$ has to divide one of the two factors
          rw [t3] at t2; apply Prime.dvd_or_dvd at t2
-- Prove by cases
          rcases t2 with t2l | t2r
          · rw [two_mul]; apply Nat.le_of_dvd at t2l; linarith
            linarith
          rw [two_mul]; apply Nat.le_of_dvd at t2r;
          have t4 : n + 1 - i ≤ n + 1 := by simp
          linarith; simp; linarith
          apply Nat.prime_iff.mp; assumption
          apply Nat.prime_iff.mp; assumption
        linarith
-- Case $p^2$ divides $(n+1)^2+1$
      | step h''k =>
        simp at h''k; rw [h''k] at hk2; simp at hk2
        rw [hk2] at hsq3; simp at hsq3; rw [hsq3] at hsq2
-- Prove that $p^2$ is less or equal to $(n+1)^2+1$, then finish the proof by contradiction
        apply Nat.le_of_dvd at hsq2; by_contra h; push_neg at h
        have u1 : ( 2 * (n + 1)) ^ 2 ≤ p ^ 2 := by
          rw [Nat.pow_le_pow_iff_left]; assumption; norm_num
        have u2 : (2 * (n + 1)) ^ 2 ≤ (n + 1) ^ 2 + 1 := by linarith
        ring_nf at u2; nth_rw 2 [show 4=3+1 by norm_num] at u2
        rw [mul_add, ← add_assoc, mul_one] at u2; simp at u2
        rw [show 4=2+2 by norm_num, add_assoc, add_assoc] at u2
        simp at u2; rw [add_comm, show 8=2+6 by norm_num] at u2
        rw [mul_add, add_assoc, add_assoc] at u2; simp at u2; simp
    assumption