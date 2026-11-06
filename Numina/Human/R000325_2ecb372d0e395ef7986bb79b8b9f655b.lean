import Mathlib

/-Ruby has a non-negative integer  $n$ . In each second, Ruby replaces the number she has with the product of all its digits. Prove that Ruby will eventually have a single-digit number or  $0$ . (e.g.  $86\rightarrow 8\times 6=48 \rightarrow 4 \times 8 =32 \rightarrow 3 \times 2=6$ )

*Proposed by Wong Jer Ren*-/
theorem number_theory_8936 (n : ℕ)(f : ℕ → ℕ)
(hf0 : f 0 = n)(hf : ∀ m, f (m + 1) = (Nat.digits 10 (f m)).prod):
∃ N, ∀ m, N < m → (Nat.digits 10 (f m)).length ≤ 1 := by
-- Prove the lemma that if $f(m)$ has one digit, then $f(m+1)$ also has one digit
  have lm0 : ∀ m, (Nat.digits 10 (f m)).length = 1 → (Nat.digits 10 (f (m+1))).length = 1 := by
    intro m hm;
    have q0 : f m ≠ 0 := by
      by_contra hne; rw [hne] at hm
      simp at hm
    have q1 := Nat.digits_len 10 (f m) (show 1<10 by norm_num) q0
    rw [hm] at q1; simp at q1
    have q2 := hf m
    have q3 : Nat.digits 10 (f m) = [f m] := by
      rw [Nat.digits_eq_cons_digits_div]; simp
      constructor
      · assumption
      have : f m / 10 = 0 := by
        rw [Nat.div_eq_zero_iff]; norm_num; assumption
      rw [this]; simp; norm_num; assumption
    rw [q3] at q2; simp at q2; rw [q2]; assumption

-- Prove the lemma that if $f(m)$ has more than one digits, then $f(m+1)$ is less than $f(m)$
  have lm1 : ∀ m, 1 < (Nat.digits 10 (f m)).length → f (m + 1) < f m := by
-- Rewrite assumptions and prepare some simple results for later use
    intro m hm
    replace hm : 2 ≤ (Nat.digits 10 (f m)).length := by linarith
    let t := (Nat.digits 10 (f m)).length - 2
    have z4 : (Nat.digits 10 (f m)).length = t + 2 := by
      simp only [t]; rw [Nat.sub_add_cancel]; assumption
    have z3 : f m ≠ 0 := by
      by_contra h'; rw [h'] at hm; simp at hm
-- Prove that the list of digits of $f(m)$ is not the nil list
    have z0 : Nat.digits 10 (f m) ≠ [] := by
      by_contra h'; rw [h', List.length_nil] at hm; linarith
    have z1 := hf m
-- Prove that the first digit of $f(m)$ is not zero
    have z2 : 0 < (Nat.digits 10 (f m)).getLast z0 := by
      have := Nat.getLast_digit_ne_zero 10 z3
      apply Nat.ne_zero_iff_zero_lt.mp; assumption
-- Rewrite the list of digits of $f(m)$ as the combine of its first digit and the rest digits
    have z6 := List.dropLast_append_getLast z0
-- Split the product of digits in the definition of $f(m+1)$
    rw [← z6, List.prod_append] at z1
    simp at z1
-- Prove that every digit is less or equal to $9$
    have z7 : ∀ x ∈ (Nat.digits 10 (f m)).dropLast, x ≤ 9 := by
      intro x hx
      apply Nat.le_of_lt_add_one; rw [show 9+1=10 by norm_num]
      have y1 := List.dropLast_subset (Nat.digits 10 (f m))
      rw [List.subset_def] at y1
      have y2 := y1 hx
      apply @Nat.digits_lt_base 10 (f m) ; norm_num; assumption
-- Prove that the product of all digits in the dropLast list is less or equal to $9^(t+1)$
    have z8 := List.prod_le_pow_card (Nat.digits 10 (f m)).dropLast 9 z7
    have z9 : (Nat.digits 10 (f m)).dropLast.length = t + 1 := by simp; assumption
    rw [z9] at z8
-- Prove that $f(m+1)$ is less or equal to the product of the first digit of $f(m)$ and $9^(t+1)$
    have z10 : f (m + 1) ≤ List.getLast (Nat.digits 10 (f m)) z0 * 9 ^ (t + 1) := by
      rw [z1, mul_comm, mul_le_mul_left]; assumption; assumption
-- Write out the 10-adic expansion of $f(m)$
    have z11 := Nat.ofDigits_eq_sum_mapIdx 10 (Nat.digits 10 (f m))
-- Split the sum and prove $f(m+1)$ is less than $f(m)$
    rw [Nat.ofDigits_digits 10 (f m), ← z6, List.mapIdx_append] at z11
    simp at z11; rw [z4, Nat.add_sub_assoc, show 2-1=1 by norm_num] at z11
    have z12 : (Nat.digits 10 (f m)).getLast z0 * 9 ^ (t + 1) < (Nat.digits 10 (f m)).getLast z0 * 10 ^ (t + 1) := by
      apply (Nat.mul_lt_mul_left z2).mpr
      rw [Nat.pow_lt_pow_iff_left]; norm_num; linarith
    have z13 : (Nat.digits 10 (f m)).getLast z0 * 10 ^ (t + 1) ≤ f m := by
      nth_rewrite 2 [z11]; simp
    linarith; norm_num

-- Rewrite assumptions and prove by contradiction
  use n; intro m hm; by_contra h; push_neg at h
-- Prove that for all $k$ less or equal to $m$, $f(k)$ has more than one digits
  have r2 : ∀ k, k ≤ m → 1 < (Nat.digits 10 (f k)).length := by
-- Use decreasing induction on $k$
    apply Nat.decreasingInduction
    · intro k _ hk2; by_contra h'; push_neg at h'
-- Prove that $f(k)$ has less digits than $f(k+1)$, therefore $f(k)$ is less than $f(k+1)$
      have t0 := hf k
      have t1 : (Nat.digits 10 (f k)).length < (Nat.digits 10 (f (k + 1))).length := by linarith
      rw [Nat.digits_len, Nat.digits_len] at t1; simp at t1
      apply Nat.lt_pow_of_log_lt (show 1<10 by norm_num) at t1
      by_cases h'' : f (k+1) ≠ 0
      have t2 := Nat.pow_log_le_self 10 h''
      have t3 : f k < f (k+1) := by linarith
-- Prove that $f(k)$ has digits less or equal to one by contradiction
      have t4 : (Nat.digits 10 (f k)).length ≤ 1 := by
        by_contra hne; push_neg at hne
        linarith
-- Apply lemma lm0 to prove that $f(k+1)$ has one digit, which is a contradiction
      rcases Nat.le_iff_lt_or_eq.mp t4 with hll | hrr
      · simp at hll; rw [hll] at t0
        simp at t0; rw [t0, Nat.digits_len, Nat.log_eq_zero_iff.mpr] at hk2
        linarith; left; norm_num; norm_num; norm_num
      · have := lm0 k hrr
        linarith
      push_neg at h''; rw [h''] at hk2; simp at hk2; norm_num
      by_contra h'ne; rw [h'ne] at hk2; simp at hk2; norm_num
      by_contra h''ne; rw [h''ne] at t0; simp at t0
      rw [t0] at hk2; simp at hk2
    · assumption
-- Apply lemma lm1 to prove that $f(i)$ is less or equal to $n-i$ for all $i$ less or equal to $n$
  have r3 : ∀ i, i ≤ n → f i ≤ n - i := by
    intro i hi; induction i with
    | zero => rw [hf0]; simp
    | succ n' ih => have v1 : n' ≤ n := by linarith
                    replace ih := ih v1
                    have v2 := r2 n' (show n' ≤ m by linarith)
                    have v4 := lm1 n' v2
                    rw [← Nat.sub_sub]; apply Nat.le_of_lt_add_one
                    rw [Nat.sub_add_cancel]; linarith; linarith
-- In particular, this means that $f(n)$ has to be $0$, contradicts to the fact that $f(n)$ has more than one digits
  have w1 := r3 n
  have w2 := r2 n (show n ≤ m by linarith)
  simp at w1; rw [w1] at w2; simp at w2
