import Mathlib

/-Determine all composite positive integers $n$ such that, for each positive divisor $d$ of $n$, there are integers $k \geq 0$ and $m \geq 2$ such that $d=k^{m}+1$.

Answer: 10.-/
theorem number_theory_605241 (n : ℕ) (npos : 0 < n) (ncomp : ¬ n.Prime ∧ n ≠ 1):
(∀ d ∈ n.divisors, ∃ k m, 2 ≤ m ∧ d = k ^ m + 1) ↔ n = 10 := by
  constructor
  -- Prove that in the assumption hd, we can actually take $m$ to be $2$
  · intro hd; replace hd : ∀ d ∈ n.divisors, ∃ k, d = k ^ 2 + 1 := by
    -- Take any divisor $d$ of $n$ and use strong induction on $d$
      intro d; induction d using Nat.strong_induction_on; rename_i d ihd
    -- Apply hd to $d$ to get $k$ and $m$
      intro ddvd; obtain ⟨k, m, ⟨_, hm⟩⟩ := hd d ddvd; by_cases mpar : Even m
      -- If $m$ is even, say it is $t+t$, then fulfill the goal with $k^t$
      · rcases mpar with ⟨t, ht⟩; use k^t; rw [hm, ht]; ring
    -- If $m$ is odd, then $k+1$ divides $d$
      rw [Nat.not_even_iff_odd] at mpar; have kdvd : k + 1 ∣ d := by
        rw [hm]; nth_rw 2 [show 1 = 1^m by simp]
        apply Odd.nat_add_dvd_pow_add_pow; exact mpar
    -- Therefore $k+1$ is a divisor of $n$
      have : (k + 1) ∈ n.divisors := by
        simp; constructor; any_goals linarith
        apply dvd_trans kdvd; simp at ddvd; exact ddvd.left
    -- If $k+1$ is strictly less than $d$, then we can apply the induction hypothesis on $k+1$ to get $l$
      by_cases hk : k + 1 < d
      · specialize ihd (k+1) hk this; rcases ihd with ⟨l, hl⟩; simp at hl
      -- Fulfill the goal with $l^m$
        use l^m; rw [hm, hl]; ring
    -- If $k+1$ equals $d$, then $k$ has to be $1$ and the goal follows
      simp at ddvd; rcases ddvd with ⟨ddvd⟩; replace hk : k + 1 = d := by
        apply Nat.le_of_dvd at kdvd; linarith
        rcases ddvd; by_contra!; simp_all
      simp [hm] at hk; symm at hk; by_cases h : 1 < k
      · rw [Nat.pow_eq_self_iff h] at hk; linarith
      interval_cases k; all_goals simp_all
      use 1; norm_num
  -- Prove that $n$ is squarefree
    have nsqfr : Squarefree n := by
    -- Assume the contrary that there exists a prime $p$ such that $p^2$ divides $n$
      rw [Nat.squarefree_iff_prime_squarefree]; intro p ppr pdvd
    -- Apply hd to $p^2$ to get $l$, then rearrange the terms of hl and rewrite it to a product form
      obtain ⟨l, hl⟩ := hd (p*p) (by simp; constructor; exact pdvd; linarith)
      rw [← Nat.sub_eq_iff_eq_add', ← pow_two, Nat.sq_sub_sq] at hl; simp at hl
    -- Find a contradiction by linarith
      have := ppr.two_le; all_goals linarith
  -- Take two different prime divisors $p< q$ of $n$ since $n$ is composite
    obtain ⟨p, q, ppr, pdvd, qpr, qdvd, pltq⟩ : ∃ p q : ℕ, p.Prime ∧ p ∣ n ∧ q.Prime ∧ q ∣ n ∧ p < q := by
      obtain ⟨ppr, pdvd⟩ := Nat.find_spec (Nat.exists_prime_and_dvd ncomp.right)
      have lepiff := Nat.find_le_iff (Nat.exists_prime_and_dvd ncomp.right)
      set p := Nat.find (Nat.exists_prime_and_dvd ncomp.right)
      have : n / p ≠ 1 := by
        intro h; simp [Nat.div_eq_iff_eq_mul_left ppr.pos pdvd] at h
        rw [h] at ncomp; rcases ncomp; contradiction
      obtain ⟨qpr, qdvd⟩ := Nat.find_spec (Nat.exists_prime_and_dvd this)
      set q := Nat.find (Nat.exists_prime_and_dvd this)
      use p; use q; split_ands; any_goals assumption
      · apply dvd_trans qdvd; use p; rw [Nat.div_mul_cancel pdvd]
      rw [lt_iff_le_and_ne]; constructor
      · apply (lepiff q).mpr; use q; simp; constructor; exact qpr
        apply dvd_trans qdvd; use p; rw [Nat.div_mul_cancel pdvd]
      intro h; rw [← h] at qdvd; rw [Nat.squarefree_iff_prime_squarefree] at nsqfr
      specialize nsqfr p ppr; rcases qdvd with ⟨w, hw⟩
      rw [Nat.div_eq_iff_eq_mul_right ppr.pos pdvd, ← mul_assoc] at hw
      have : p * p ∣ n := by use w
      contradiction
  -- Prove that for any two prime factors $p$, $q$ of $n$ with $p< q$, $p$ has to be $2$ and $1$ has to be $5$
    have pqaux : ∀ p q : ℕ, p.Prime → p ∣ n → q.Prime → q ∣ n → p < q → (p = 2 ∧ q = 5) := by
      intro p q ppr pdvd qpr qdvd pltq
  -- Apply hd to $p$, $q$ and $p*q$ respectively to get numbers $a$, $b$ and $c$
      obtain ⟨a, ha⟩ := hd p (by simp; constructor; exact pdvd; linarith)
      obtain ⟨b, hb⟩ := hd q (by simp; constructor; exact qdvd; linarith)
      have pqdvd : p * q ∣ n := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd; rw [Nat.coprime_primes ppr qpr]
        linarith; all_goals assumption
      obtain ⟨c, hc⟩ := hd (p*q) (by simp; constructor; exact pqdvd; linarith)
      have := ppr.two_le
    -- Prove some positivity results we need
      have apos : 0 < a := by by_contra!; simp at this; simp [this] at ha; linarith
      have bpos : 0 < b := by by_contra!; simp at this; simp [this] at hb; linarith
      have cpos : 0 < c := by by_contra!; simp at this; simp [this] at hc; linarith
    -- Prove that $a$ is less than $b$
      have altb : a < b := by
        rw [← pow_lt_pow_iff_left₀ (by simp) (by simp) (show 2≠0 by simp), ← add_lt_add_iff_right 1]
        rw [← ha, ← hb]; exact pltq
    -- Prove that $b$ is less than $c$
      have bltc : b < c := by
        rw [← pow_lt_pow_iff_left₀ (by simp) (by simp) (show 2≠0 by simp), ← add_lt_add_iff_right 1]
        rw [← hb, ← hc, Nat.lt_mul_iff_one_lt_left]; all_goals linarith
    -- Prove that $c$ is less than $q$
      have cltq : c < q := by
        rw [← pow_lt_pow_iff_left₀ (by simp) (by simp) (show 2≠0 by simp), ← add_lt_add_iff_right 1]
        rw [← hc]; apply Nat.lt_add_right; rw [pow_two, mul_lt_mul_right]; all_goals linarith
    -- Prove that $q$ divides $c+b$ or $c-b$
      apply_fun fun t => t - q at hc; nth_rw 3 [hb] at hc; rw [Nat.add_sub_add_right, Nat.sq_sub_sq] at hc
      rw [← Nat.sub_one_mul] at hc; have : q ∣ (c + b) * (c - b) := by simp [← hc]
      rw [qpr.dvd_mul] at this; rcases this with hl|hr
      -- If $q$ divides $c+b$, prove that $c$ is equal to $q-b$
      · rcases hl with ⟨w, hw⟩; have : 0 < w := by
          by_contra!; simp at this; simp [this] at hw; linarith
        have : w < 2 := by rw [← mul_lt_mul_left (show 0<q by linarith)]; linarith
        replace this : w = 1 := by linarith
        rw [this, mul_one] at hw; symm at hw; rw [← Nat.sub_eq_iff_eq_add] at hw
      -- Plug in $c=q-b$ to hc and rearrange its term
        rw [← hw, Nat.sub_add_cancel, mul_comm] at hc; apply mul_left_cancel₀ at hc
        rw [Nat.sub_eq_iff_eq_add, Nat.sub_sub, ← two_mul] at hc
      -- Prove that $p=2$ by showing $p$ is even from hc
        have peq : p = 2 := by
          rw [← ppr.even_iff, hc, Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_sub]
          simp; exact qpr.odd_of_ne_two (by linarith)
          apply le_of_lt; rw [← Nat.sub_pos_iff_lt, ← add_lt_add_iff_right 1, ← hc]; linarith
      -- Plug in $p=2$ and hb to hc and prove $b=2$
        zify at hc; rw [Nat.cast_sub, hb, peq, ← sub_eq_zero] at hc; push_cast at hc; ring_nf at hc
        simp [pow_two, ← mul_sub] at hc; rcases hc with _|beq; linarith
        rw [sub_eq_zero] at beq; norm_cast at beq; simp [← beq] at hb
        constructor; any_goals linarith
        apply le_of_lt; norm_cast at hc
        rw [← Nat.sub_pos_iff_lt, ← add_lt_add_iff_right 1, ← hc]; linarith
    -- If $q$ divides $c-b$, we can find a contradicion by linarith
      apply Nat.le_of_dvd at hr; rw [Nat.le_sub_iff_add_le] at hr; any_goals linarith
      rw [Nat.sub_pos_iff_lt]; all_goals linarith
  -- Specialize pqaux to $p$ and $q$, we get $p=2$ and $q=5$
    have pqeq := pqaux p q ppr pdvd qpr qdvd pltq
    rw [pqeq.left] at pdvd; rw [pqeq.right] at qdvd
  -- Prove that $10$ divides $n$
    have tendvd : 10 ∣ n := by
      rw [show 10 = 2*5 by simp]; apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      norm_num; all_goals assumption
  -- Rewrite the equality goal to two inequalities
    symm; rw [eq_iff_le_not_lt]; constructor
    -- Prove $10≤n$ from $10$ divides $n$
    · apply Nat.le_of_dvd; exact npos; exact tendvd
  -- Assume the contrary that $n$ is greater than $10$, then we can take any prime divisor $r$ of $n/10$
    intro h; have : 1 < n / 10 := by
      rw [Nat.lt_div_iff_mul_lt']; linarith; exact tendvd
    obtain ⟨r, ⟨rpr, rdvd⟩⟩ := Nat.exists_prime_and_dvd (show n/10 ≠ 1 by linarith)
  -- Rewrite nsqfr and apply it on $2$ and $5$
    rw [Nat.squarefree_iff_prime_squarefree] at nsqfr; have := nsqfr 2 Nat.prime_two
    have := nsqfr 5 Nat.prime_five; by_cases h' : r = 2
    -- If $r=2$, then we have $2^2$ divides $n$, contradicting to the fact that $n$ is squarefree
    · rcases rdvd with ⟨w, hw⟩; rw [Nat.div_eq_iff_eq_mul_right (by simp) tendvd, h'] at hw
      have : 2 * 2 ∣ n := by use 5*w; rw [hw]; ring
      contradiction
  -- If $r$ is not $2$, applying pqaux on $2$ and $r$ shows $r=5$, then we have $5^2$ divides $n$
  -- contradicting to to the fact that $n$ is squarefree
    replace h' : 2 < r := by apply Nat.lt_of_le_of_ne; exact rpr.two_le; exact Ne.symm h'
    have : r ∣ n := by apply dvd_trans rdvd; use 10; rw [Nat.div_mul_cancel tendvd]
    obtain ⟨_,req⟩ := pqaux 2 r Nat.prime_two pdvd rpr this h'
    rcases rdvd with ⟨w, hw⟩; rw [Nat.div_eq_iff_eq_mul_right (by simp) tendvd, req] at hw
    have : 5 * 5 ∣ n := by use 2*w; rw [hw]; ring
    contradiction
-- Conversely, it is straightforward to check that if $n=10$, all of its divisors can be written in the desired form
  intro neq; rw [neq, show Nat.divisors 10 = {1, 2, 5, 10} by decide]; simp; split_ands
  · use 0; use 2; simp
  · use 1; use 2; simp
  · use 2; use 2; simp
  · use 3; use 2; simp