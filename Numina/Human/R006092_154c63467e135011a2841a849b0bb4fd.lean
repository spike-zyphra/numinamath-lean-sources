import Mathlib
/- Find the largest positive integer $n$ such that $1!+2!+3!+\cdots+n$ ! is a perfect square. Prove that your answer is correct. -/
theorem number_theory_611546 : IsGreatest {n : ℕ | ∃ k : ℕ, ∑ i in Finset.range n, (i + 1).factorial = k ^ 2} 3:= by
  -- We need to prove two things: 1) 3 is in the set, and 2) 3 is an upper bound of the set
  constructor
  -- First, prove that 3 is in the set, i.e., 1! + 2! + 3! is a perfect square
  .
    simp
    use 3
    simp [Finset.sum_range_succ]
    rw [Nat.factorial_succ]
    simp
  -- Second, prove that 3 is an upper bound of the set
  .
    simp [upperBounds]
    intro n k h
    -- We'll use proof by contradiction
    by_contra H
    simp at H
    -- Rewrite n as (n-1)+1 to extract the last term n!
    rw [show n = (n - 1) + 1 by omega] at h
    rw [Finset.sum_range_succ' (fun i => (i + 1).factorial) _] at h
    -- Rewrite (n-1) as (n-2)+1 to extract the term (n-1)!
    rw [show n - 1 = n - 2 + 1 by omega] at h
    rw [Finset.sum_range_succ' (fun i => (i + 1 + 1).factorial) _] at h
    -- Rewrite (n-2) as (n-3)+1 to extract the term (n-2)!
    rw [show n - 2 = n - 3 + 1 by omega] at h
    rw [Finset.sum_range_succ' (fun i => (i + 1 + 1 + 1).factorial) _] at h
    -- Rewrite (n-3) as (n-4)+1 to extract the term (n-3)!
    rw [show n - 3 = n - 4 + 1 by omega] at h
    rw [Finset.sum_range_succ' (fun i => (i + 1 + 1 + 1 + 1).factorial) _] at h
    simp at h
    -- Prove that 5 divides k! for all k ≥ 5
    have h1 : ∀ k ∈ Finset.range (n - 4), 5 ∣ (k + 1 + 1 + 1 + 1 + 1).factorial:= by
      intro k _
      ring_nf
      simp [Nat.dvd_factorial]
    -- Therefore 5 divides the sum of all factorials from 5! to n!
    replace h1 : 5 ∣ ∑ k ∈ Finset.range (n - 4), (k + 1 + 1 + 1 + 1 + 1).factorial:= by exact Finset.dvd_sum h1
    -- Define t as the sum of factorials from 5! to n!
    set t:= ∑ k ∈ Finset.range (n - 4), (k + 1 + 1 + 1 + 1 + 1).factorial with ht
    clear_value t
    -- Rewrite the sum 1! + 2! + ... + n! as t + (4! + 3! + 2! + 1!)
    rw [show t + Nat.factorial 4 + Nat.factorial 3 + 2 + 1 = t + (Nat.factorial 4 + Nat.factorial 3 + 2 + 1) by ring] at h
    -- Calculate that 4! + 3! + 2! + 1! ≡ 3 (mod 5)
    have h2 : Nat.factorial 4 + Nat.factorial 3 + 2 + 1 ≡ 3 [MOD 5]:= by
      simp [Nat.factorial_succ]
      rfl
    -- Since 5 divides t, t ≡ 0 (mod 5)
    replace h1 : t ≡ 0 [MOD 5]:= by exact Nat.modEq_zero_iff_dvd.mpr h1
    -- Therefore t + (4! + 3! + 2! + 1!) ≡ 0 + 3 ≡ 3 (mod 5)
    replace h1 : t + (Nat.factorial 4 + Nat.factorial 3 + 2 + 1) ≡ 0 + 3 [MOD 5]:= by exact Nat.ModEq.add h1 h2
    -- But this sum equals k², so k² ≡ 3 (mod 5)
    rw [h] at h1
    simp at h1
    -- We'll check all possible values of k modulo 5 to show that k² ≡ 3 (mod 5) is impossible
    mod_cases k % 5
    -- Case k ≡ 0 (mod 5)
    .
      replace H : k ^ 2 ≡ 0 ^ 2 [MOD 5]:= by exact Nat.ModEq.pow 2 H
      simp at H
      replace H : 0 ≡ 3 [MOD 5]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
      simp [Nat.ModEq] at H
    -- Case k ≡ 1 (mod 5)
    .
      replace H : k ^ 2 ≡ 1 ^ 2 [MOD 5]:= by exact Nat.ModEq.pow 2 H
      simp at H
      replace H : 1 ≡ 3 [MOD 5]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
      simp [Nat.ModEq] at H
    -- Case k ≡ 2 (mod 5)
    .
      replace H : k ^ 2 ≡ 2 ^ 2 [MOD 5]:= by exact Nat.ModEq.pow 2 H
      simp at H
      replace H : 4 ≡ 3 [MOD 5]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
      simp [Nat.ModEq] at H
    -- Case k ≡ 3 (mod 5)
    .
      replace H : k ^ 2 ≡ 3 ^ 2 [MOD 5]:= by exact Nat.ModEq.pow 2 H
      simp at H
      replace H : 9 ≡ 3 [MOD 5]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
      simp [Nat.ModEq] at H
    -- Case k ≡ 4 (mod 5)
    .
      replace H : k ^ 2 ≡ 4 ^ 2 [MOD 5]:= by exact Nat.ModEq.pow 2 H
      simp at H
      replace H : 16 ≡ 3 [MOD 5]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm H)) h1
      simp [Nat.ModEq] at H
