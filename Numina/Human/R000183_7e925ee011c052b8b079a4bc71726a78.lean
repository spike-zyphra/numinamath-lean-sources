import Mathlib

/-Determine the natural numbers  $m,n$  such as  $85^m-n^4=4$-/
theorem number_theory_8505_1 (m n : ℕ) (hmn : 85 ^ m - n ^ 4 = 4) :
2 ≤ n ∧ n ≤ 4 := by
-- Prepare some simple facts for later use
  have hm1 : 1 ≤ m := by
    by_contra h'; simp at h'; rw [h'] at hmn; simp at hmn
    have := Nat.sub_le 1 (n^4)
    rw [hmn] at this; linarith
  have hn1 : 2 ≤ n := by
    have := Nat.le_self_pow (show m≠0 by linarith) 85
    by_contra h'; simp at h'; cases h' with
    | refl => simp at hmn; linarith
    | step h' => simp at h'; rw [h'] at hmn; simp at hmn; linarith
-- Rewrite assumptions and factorize $n^4+4$
  have h'mn := (@Nat.add_right_cancel_iff (85 ^ m - n ^ 4) 4 (n ^ 4)).mpr hmn
  rw [Nat.sub_add_cancel, show 85=5*17 by simp, mul_pow] at h'mn
  have : 4 + n ^ 4 = (n ^ 2 + 2 + 2 * n ) * (n ^ 2 + 2 - 2 * n) := by
    rw [← Nat.sq_sub_sq, add_sq]; nth_rw 2 [add_comm]
    rw [← add_assoc, show 2^2=4 by simp, ← pow_mul, show 2*2=4 by simp]
    rw [mul_comm, ← mul_assoc, show 2*2=4 by simp, show (2*n)^2=4*n^2 by ring]
    rw [Nat.add_sub_cancel]
-- Apply the key result mul_eq_mul_prime_pow to get more information about the two factors of $n^4+4$
  rw [this] at h'mn; symm at h'mn; apply mul_eq_mul_prime_pow at h'mn
  rcases h'mn with ⟨a,b,u,v,h1,h2,h3,h4⟩; symm at h2; rw [← one_mul (5 ^ m)] at h2
  apply mul_eq_mul_prime_pow at h2
  rcases h2 with ⟨c,d,x,y,h'1,h'2,h'3,h'4⟩; symm at h'2
  rw [mul_eq_one] at h'2; rcases h'2 with ⟨h'2l,h'2r⟩
  rw [h'2l] at h'3; simp at h'3; rw [h'2r] at h'4; simp at h'4
  rw [h'3] at h3; rw [h'4] at h4
-- Show that $c$ and $d$ can't both be greater or equal to one
  by_cases hcd : 1 ≤ c ∧ 1 ≤ d
  · have d5 : 5 ∣ n ^ 2 + 2 + 2 * n := by
      use 5^(c-1)*17^a; rw [← mul_assoc]; nth_rw 1 [show 5=5^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel']; assumption; exact hcd.left
    have d'5 : 5 ∣ n ^ 2 + 2 - 2 * n := by
      use 5^(d-1)*17^b; rw [← mul_assoc]; nth_rw 1 [show 5=5^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel']; assumption; exact hcd.right
    have := Nat.dvd_sub (show n^2+2-2*n≤n^2+2+2*n by simp;linarith) d5 d'5
    rw [Nat.add_sub_sub_cancel, ← two_mul, ← mul_assoc, show 2*2=4 by simp] at this
    apply Prime.dvd_or_dvd at this; rcases this with h' | h'
    · contradiction
    have : 5 ∣ 85 ^ m - n ^ 4 := by
      apply Nat.dvd_sub; apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt]
      rw [hmn]; norm_num; use 5^(m-1)*17^m; rw [← mul_assoc]; nth_rw 1 [show 5=5^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel', ← Nat.mul_pow]; assumption
      rw [Prime.dvd_pow_iff_dvd]; assumption; rw [← Nat.prime_iff]
      norm_num; norm_num
    rw [hmn] at this; contradiction; rw [← Nat.prime_iff]; norm_num
    nth_rw 1 [show n=n*1 by simp]; rw [← mul_assoc]
    have : 2 * n * 1 ≤ n ^ 2 + 1 ^ 2 := by apply two_mul_le_add_sq
    linarith
-- Similarly, show that $a$ and $b$ can't both be greater or equal to one
  simp at hcd; by_cases hab : 1 ≤ a ∧ 1 ≤ b
  · have d17 : 17 ∣ n ^ 2 + 2 + 2 * n := by
      use 17^(a-1)*5^c; rw [← mul_assoc]; nth_rw 1 [show 17=17^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel', h3, mul_comm]; exact hab.left
    have d'17 : 17 ∣ n ^ 2 + 2 - 2 * n := by
      use 17^(b-1)*5^d; rw [← mul_assoc]; nth_rw 1 [show 17=17^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel', h4, mul_comm]; exact hab.right
    have := Nat.dvd_sub (show n^2+2-2*n≤n^2+2+2*n by simp;linarith) d17 d'17
    rw [Nat.add_sub_sub_cancel, ← two_mul, ← mul_assoc, show 2*2=4 by simp] at this
    apply Prime.dvd_or_dvd at this; rcases this with h' | h'
    · contradiction
    have : 17 ∣ 85 ^ m - n ^ 4 := by
      apply Nat.dvd_sub; apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt]
      rw [hmn]; norm_num; use 17^(m-1)*5^m; rw [← mul_assoc]; nth_rw 1 [show 17=17^1 by simp]
      rw [← pow_add, Nat.add_sub_cancel', ← Nat.mul_pow]; assumption
      rw [Prime.dvd_pow_iff_dvd]; assumption; rw [← Nat.prime_iff]
      norm_num; norm_num
    rw [hmn] at this; contradiction; rw [← Nat.prime_iff]; norm_num
    nth_rw 1 [show n=n*1 by simp]; rw [← mul_assoc]
    have : 2 * n * 1 ≤ n ^ 2 + 1 ^ 2 := by apply two_mul_le_add_sq
    linarith

-- Prove by cases, assume that $1≤c$ and $1≤a$, we prove that $n$ has to be $1$, which is a contradiction
  simp at hab; by_cases hc : 1 ≤ c
  · have hd := hcd hc
    rw [hd] at h4; rw [hd] at h'1; simp at h'1; simp at h4
    rw [h'1] at h3; by_cases ha : 1 ≤ a
    · have hb := hab ha
      rw [hb] at h4; simp at h4
      have : n ^ 2 + 2 - 2 * n = (n - 1) ^ 2 + 1 := by
        rw [Nat.sub_add_comm]; nth_rw 3 [show 2=1+1 by simp]
        rw [← add_assoc, Nat.add_right_cancel_iff]
        nth_rw 2 [pow_two]; rw [Nat.mul_sub, mul_one, Nat.sub_mul, one_mul]
        rw [Nat.sub_sub, ← Nat.add_sub_assoc, ← two_mul, ← pow_two]
        nth_rw 1 [show 2*n=2*n-1+1 by rw [Nat.sub_one_add_one];linarith]
        rw [Nat.sub_add_eq]; nth_rw 1 [Nat.sub_one_add_one]
        rw [Nat.ne_zero_iff_zero_lt, Nat.lt_sub_iff_add_lt]; simp
        have : 2 * n - 1 < 2 * n := by simp; linarith
        have : 2 * n ≤ n ^ 2 := by rw [pow_two]; apply Nat.mul_le_mul_right; linarith
        linarith; linarith; rw [pow_two]; apply Nat.mul_le_mul_right; linarith
      rw [this] at h4; simp at h4; rw [Nat.sub_eq_iff_eq_add] at h4
      simp at h4; linarith; linarith
-- Assume $c$ is greater or equal to $1$ and $a$ is $0$, we will reach a contradiction
    simp at ha; rw [ha] at h1; simp at h1; rw [h1] at h4
    rw [ha] at h3; simp at h3
    have : n ^ 2 + 2 - 2 * n ≤ n ^ 2 + 2 + 2 * n := by
      have : n ^ 2 + 2 - 2 * n ≤ n ^ 2 + 2 := by simp
      linarith
    have : n ^ 2 + 2 + 2 * n < n ^ 2 + 2 - 2 * n := by
      rw [h3, h4, Nat.pow_lt_pow_iff_left]; norm_num; linarith
    linarith
-- Case: $c$ is $0$ and $a$ is greater or equal to $1$. In this case, we will get an upper bound on $n$
  simp at hc; rw [hc] at h'1; simp at h'1
  rw [hc] at h3; simp at h3; rw [h'1] at h4
  by_cases ha : 1 ≤ a
  · have hb := hab ha
    rw [hb] at h4; simp at h4; rw [hb] at h1; simp at h1; rw [h1] at h3
    have r1 : 3 * 5 ^ m < 17 ^ m := by
      have : 3 ≤ 3 ^ m := by
        nth_rw 1 [show 3=3^1 by simp]; rw [Nat.pow_le_pow_iff_right]; linarith; norm_num
      have : 3 ^ m * 5 ^ m = 15 ^ m := by
        rw [show 15=3*5 by simp, mul_pow]
      have : 15 ^ m < 17 ^ m := by rw [Nat.pow_lt_pow_iff_left]; norm_num; linarith
      have : 3 * 5 ^ m ≤ 3 ^ m * 5 ^ m := by
        apply Nat.mul_le_mul; assumption; simp
      linarith
    rw [← h4, ← h3] at r1; constructor
    · assumption
    by_contra h'; simp at h'; rw [Nat.mul_sub, ← mul_assoc] at r1; simp at r1
    rw [Nat.sub_lt_iff_lt_add, mul_add] at r1; ring_nf at r1
    rw [show 3=2+1 by simp, mul_add, mul_one,← add_assoc] at r1; simp at r1
    have : 2 + n * 8 < 6 + n ^ 2 * 2 := by
      apply Nat.add_lt_add
      · norm_num
      rw [show 8=4*2 by norm_num, ← mul_assoc]; simp
      rw [pow_two, Nat.mul_lt_mul_left]; assumption; linarith
    linarith; rw [show 6=3*2 by simp, mul_assoc]; simp
    have : 2 * n * 1 ≤ n ^ 2 + 1 ^ 2 := by apply two_mul_le_add_pow_two
    linarith
-- Case: $c$ is $0$ and $a$ is $0$. We will reach a contradiction
  simp at ha; rw [ha] at h3; simp at h3
  rw [show n^2+2+2*n=(n+1)^2+1 by ring] at h3; simp at h3
  rw [← Nat.prime_iff]; norm_num; rw [← Nat.prime_iff]; norm_num
  apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt, hmn]; norm_num
-- Therefore, we only need to check the cases when $n$ equals $2$, $3$ or $4$.
-- It is not hard to find that the only solution is $m=1$ and $n=3$

/-Determine the natural numbers  $m,n$  such as  $85^m-n^4=4$-/
theorem number_theory_8505_2 : ∀ m n: ℕ, 85 ^ m - n ^ 4 = 4 ↔ m = 1 ∧ n = 3 := by
-- Introduce variables and assumptions, split "iff"
  intro m n; constructor
  · intro hmn
-- Prove that $m$ is greater or equal to $1$
    have hm1 : 1 ≤ m := by
      by_contra h'; simp at h'; rw [h'] at hmn; simp at hmn
      have := Nat.sub_le 1 (n^4)
      rw [hmn] at this; linarith
    have : 85 ^ 1 ≤ 85 ^ m := by
      rw [Nat.pow_le_pow_iff_right]; assumption; norm_num
-- Apply number_theory_8505_1 to get bounds for $n$
    obtain ⟨nl, nr⟩ := number_theory_8505_1 m n hmn
-- Split the goal to cases when $n$ is $2$, $3$ or $4$
    interval_cases n
    all_goals simp_all; rw [Nat.sub_eq_iff_eq_add] at hmn; norm_num at hmn
-- The first case is ruled out since $85^m$ is greater or equal to $85$
    linarith; linarith
-- In the second case, we can easily solve for $m$
    nth_rw 2 [show 85=85^1 by simp] at hmn
    apply Nat.pow_right_injective at hmn; assumption; norm_num; linarith
-- In the third case, we first prove that $m$ is less than $2$,
-- then rule out the case when $m$ is $1$
    · have : m < 2 := by
        by_contra h'; push_neg at h'
        have : 85 ^ 2 ≤ 85 ^ m := by
          rw [Nat.pow_le_pow_iff_right]; assumption; norm_num
        linarith
      replace this : m = 1 := by linarith
      simp_all
    apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt, hmn]; norm_num
-- Conversely, it is a straightfoward computation to check that
-- $m=1$, $n=3$ is a solution to our problem
  rintro ⟨⟩; simp_all