import Mathlib

/- Let $f: \mathbb{Z}_{>0} \rightarrow \mathbb{R}$ be a function such that for all $n>1$ if there is
a prime divisor $p$ of $n$ then
$$
f(n)=f\left(\frac{n}{p}\right)-f(p).
$$
Furthermore, it is given that $f\left(2^{2014}\right)+f\left(3^{2015}\right)+f\left(5^{2016}\right)=2013$.
Calculate $f\left(2014^{2}\right)+f\left(2015^{3}\right)+f\left(2016^{5}\right)$.
Answer: $\frac{49}{3}$. -/
theorem number_theory_605413 (f : ℕ → ℝ)
    (h : ∀ (n p : ℕ), (Nat.Prime p ∧ p ∣ n) → f n = f (n / p) - f p)
    (h' : f (2 ^ 2014) + f (3 ^ 2015) + f (5 ^ 2016) = 2013) :
    f (2014 ^ 2) + f (2015 ^ 3) + f (2016 ^ 5) = 49 / 3 := by

  -- When $n=q$ with $q$ prime, there is only one prime divisor of $n$, namely $q$, so it must hold
  -- that $f(q)=f(1)-f(q)$, thus $f(q)=\frac{1}{2} f(1)$.
  have q_pow_prime_aux_1 (q : ℕ) (hq : Nat.Prime q) : f q = (f 1) / 2 := by
    have hfq := h q q (by simp [hq])
    have : q / q = 1 := by
      exact Nat.div_self <| Nat.zero_lt_of_lt (Nat.Prime.one_lt hq)
    rw [this] at hfq
    linarith

  -- If $n=q^{2}$ with $q$ prime, then $n$ also has only one prime divisor,
  -- so $f\left(q^{2}\right)=f(q)-f(q)=0$.
  have q_pow_prime_aux_2 (q : ℕ) (hq : Nat.Prime q) : f (q ^ 2) = 0 := by
    have : Nat.Prime q ∧ q ∣ q ^ 2 := by
      exact And.symm ⟨Dvd.intro_left (q.pow 1) rfl, hq⟩
    have hfq := h (q ^ 2) q this
    have : q ^ 2 / q = q := by
      rw [pow_two]
      apply Nat.mul_div_cancel
      exact Nat.Prime.pos hq
    rw [this] at hfq
    linarith

  -- We now prove by induction on $k$ that $f\left(q^{k}\right)=\frac{2-k}{2} f(1)$ if $q$ is a
  -- prime number and $k$ is a positive integer.
  have q_pow_prime (q : ℕ) (k : ℕ) (hk : 0 < k) (hq : Nat.Prime q) : f (q ^ k) = (f 1) * (2 - k) / 2 := by
    obtain hc | hc : k = 1 ∨ 1 < k := by omega
    · -- For $k=1$ we have already shown this.
      rw [hc, pow_one]
      linarith [q_pow_prime_aux_1 q hq]
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := by exact Nat.exists_eq_add_of_le' hc
      rw [hj]
      clear hj
      induction j with
      | zero =>
        -- For $k=2$, we have already shown this.
        simp only [zero_add, Nat.cast_ofNat, sub_self, mul_zero, zero_div]
        exact q_pow_prime_aux_2 q hq
      | succ j hi =>
        -- Suppose now that $f\left(q^{k}\right)=\frac{2-k}{2} f(1)$ for some $k \geq 2$ and substitute $n=q^{k+1}$.
        -- It holds that
        -- $$ f\left(q^{k+1}\right)=f\left(q^{k}\right)-f(q)=\frac{2-k}{2} f(1)-\frac{1}{2} f(1)=\frac{2-(k+1)}{2} f(1) $$
        calc
          _ = f (q ^ (j + 2)) - f q := by
            -- using `h` since `q` is prime and divides `q ^ (j + 1 + 2)`
            have hfq := h (q ^ (j + 1 + 2)) q ⟨hq, Dvd.intro_left (q.pow (j + 2)) rfl⟩
            have : q ^ (j + 1 + 2) / q = q ^ (j + 2) := by
              rw [show q ^ (j + 1 + 2) = q ^ (j + 2) * q by rfl]
              apply Nat.mul_div_cancel
              exact Nat.Prime.pos hq
            rw [this] at hfq
            linarith
          _ = f 1 * (2 - ↑(j + 2)) / 2 - f q := by
            -- using the inductive hypothesis
            rw [hi]
          _ = _ := by
            -- using the case when `n` is prime
            rw [q_pow_prime_aux_1 q hq]
            simp only [Nat.cast_add, Nat.cast_ofNat, sub_add_cancel_right, mul_neg, Nat.cast_one,
              neg_add_rev]
            linarith

  -- It holds that $f(1)=-\frac{2}{3}$.
  have f_one : f 1 = -2 / 3 := by
    -- $2013 =f\left(2^{2014}\right)+f\left(3^{2015}\right)+f\left(5^{2016}\right)
    -- = \frac{2-2014}{2} f(1)+\frac{2-2015}{2} f(1)+\frac{2-2016}{2} f(1)
    -- =-\frac{6039}{2} f(1)$$
    -- so $f(1)=\frac{2013 \cdot 2}{-6039}=-\frac{2}{3}$.
    have := calc 2013
      _ = f (2 ^ 2014) + f (3 ^ 2015) + f (5 ^ 2016) := Eq.symm h'
      _ = (f 1) * (2 - 2014) / 2 + (f 1) * (2 - 2015) / 2 +  (f 1) * (2 - 2016) / 2 := by
        rw [q_pow_prime 2 2014 (by omega) (by decide)]
        rw [q_pow_prime 3 2015 (by omega) (by decide)]
        rw [q_pow_prime 5 2016 (by omega) (by decide)]
        simp
      _ = (f 1) * (-6039) / 2 := by
        linarith
    linarith

  -- We then prove that if $n=p_{1} p_{2} \cdots p_{m}$ with $p_{1}, p_{2}, \ldots, p_{m}$ not
  -- necessarily distinct primes and $m \geq 0$, then $f(n)=\frac{m-2}{3}$.
  have f_prod_prime {m : ℕ} : ∀ n : ℕ,
      (∃ (p : Fin m → ℕ), (n = ∏ i, p i) ∧ (∀ i, Nat.Prime (p i))) → f n = (m - 2) / 3 := by
    -- We do this by induction on $m$.
    induction m with
    | zero =>
      -- For $m=0$, $n=1$ and $f(1)=-\frac{2}{3}=\frac{0-2}{3}$, so it holds for this case.
      intro n hn
      simp only [Finset.univ_eq_empty, Finset.prod_empty, IsEmpty.forall_iff, and_true,
        exists_const] at hn
      simp [hn, f_one]
    | succ m hi =>
      -- Suppose now that we have proven it for some $m \geq 0$.
      intro n hn
      -- Consider any $n$ of the form $n=p_{1} p_{2} \cdots p_{m+1}$.
      obtain ⟨p, hnp⟩ := hn
      let p' : Fin m → ℕ := by
        intro i
        exact p (i : ℕ)
      let n' := ∏ i, p' i
      have h_n_n' : n = n' * (p m) := by
        dsimp [n', p']
        rw [hnp.1]
        simpa using Fin.prod_univ_castSucc p
      have exists_p' : ∃ p : Fin m → ℕ, n' = ∏ i : Fin m, p i ∧ ∀ (i : Fin m), Nat.Prime (p i) := by
        use p'
        refine ⟨by omega, ?_⟩
        intro i
        exact hnp.2 i
      -- Then $n > 1$, so there is a prime factor $p \mid n$ for which $f(n)=f\left(\frac{n}{p}\right)-f(p)$; without loss of generality, this is $p=p_{m+1}$.
      -- It follows that
      -- $$ f(n)=f\left(p_{1} p_{2} \cdots p_{m}\right)-f\left(p_{m+1}\right)=\frac{m-2}{3}--\frac{1}{3}=\frac{(m+1)-2}{3} . $$
      calc
      _ = f (n / p m) - f (p m) := by
        have : p m ∣ n := by
          exact Dvd.intro_left n' (id (Eq.symm h_n_n'))
        exact h n (p m) ⟨hnp.2 m, this⟩
      _ = _ := by
        have : n / p m = n' := by
          -- follows from definition of `n'`
          rw [h_n_n']
          -- basic division
          apply Nat.mul_div_cancel
          exact Nat.Prime.pos (hnp.2 m)
        rw [this, q_pow_prime_aux_1 (p m) (hnp.2 m), f_one, hi n' exists_p']
        norm_num
        ring

  -- We can now calculate the desired result.

  have val_2014 : ∃ (p : Fin 6 → ℕ), (2014 ^ 2 = ∏ i, p i) ∧ (∀ i, Nat.Prime (p i)) := by
    -- The prime factorization of 2014 is $2014=2 \cdot 19 \cdot 53$.
    let a := [2, 19, 53,
              2, 19, 53]
    use fun i ↦ a[i]
    decide

  have val_2015 : ∃ (p : Fin 9 → ℕ), (2015 ^ 3 = ∏ i, p i) ∧ (∀ i, Nat.Prime (p i)) := by
    -- The prime factorization of 2015 is $2015=5 \cdot 13 \cdot 31$.
    let a := [5, 13, 31,
              5, 13, 31,
              5, 13, 31]
    use fun i ↦ a[i]
    decide

  have val_2016 : ∃ (p : Fin 40 → ℕ), (2016 ^ 5 = ∏ i, p i) ∧ (∀ i, Nat.Prime (p i)) := by
    -- The prime factorization of 2016 is $2016=2^{5} \cdot 3^{2} \cdot 7$.
    let a := [2, 2, 2, 2, 2, 3, 3, 7,
              2, 2, 2, 2, 2, 3, 3, 7,
              2, 2, 2, 2, 2, 3, 3, 7,
              2, 2, 2, 2, 2, 3, 3, 7,
              2, 2, 2, 2, 2, 3, 3, 7]
    use fun i ↦ a[i]
    decide

  -- so $$ f\left(2014^{2}\right)+f\left(2015^{3}\right)+f\left(2016^{5}\right)=
  -- \frac{6-2}{3}+\frac{9-2}{3}+\frac{40-2}{3}=\frac{49}{3} . $$
  rw [f_prod_prime (2014 ^ 2) val_2014, f_prod_prime (2015 ^ 3) val_2015,
    f_prod_prime (2016 ^ 5) val_2016]
  linarith
