import Mathlib
set_option maxHeartbeats 0

open Finset ArithmeticFunction

/-Let $N$ be an integer greater than 1, with prime factorization $N = p_1^{a_1} p_2^{a_2} \dots p_k^{a_k}$ (where $p_i$ are distinct primes and $a_i \ge 1$ for all $i=1, \dots, k$).
A function $g: \mathbb{N}^+ \rightarrow \mathbb{N}^+$ (where $\mathbb{N}^+$ is the set of positive integers) satisfies the following conditions:
(a) If $m$ is a proper divisor of $n$ (i.e., $m|n$ and $m < n$), then $g(m) < g(n)$.
(b) If $m$ and $n$ are relatively prime and $m, n > 1$, then $g(m n)=g(m) g(n)+(n+1) g(m)+(m+1) g(n)+m+n$.
Show that the least possible value of $g(N)$ is $\left(\prod_{i=1}^k (a_i+p_i^{a_i}+2)\right) - N - 1$.-/
theorem number_theory_639232 (N : ℕ) (Ngt : 1 < N) : IsLeast {t | ∃ g : ℕ → ℕ, t = g N ∧
    (∀ m ≠ 0, g m ≠ 0) ∧ (∀ m n, m < n → m ∣ n → g m < g n) ∧ (∀ m > 1, ∀ n > 1, m.Coprime n → g (m * n)
    = g m * g n + (n + 1) * g m + (m + 1) * g n + m + n)} (∏ p ∈ N.primeFactors, (N.factorization p
    + p ^ N.factorization p + 2) - N - 1) := by
  simp [IsLeast, lowerBounds]; constructor
  -- Fulfill the existential goal with the function $g(i) = i.factorization.prod (fun p e => e + p ^ e + 2) - i - 1$ for $i ≠ 1$ and $g(1)=1$
  · set g : ℕ → ℕ := fun i => if i ≠ 1 then i.factorization.prod (fun p e => e + p ^ e + 2) - i - 1 else 1
    have g1 : g 1 = 1 := by simp [g]
  -- Prove that $g(m)$ is greater than $1$ when $m > 1$
    have ggt : ∀ m > 1, 1 < g m := by
      intro m mpos
      simp [g, Finsupp.prod]
      have : m.primeFactors.Nonempty := by simp; omega
      rcases this with ⟨q, hq⟩
      rw [ite_cond_eq_false, Nat.sub_sub]
      rw [Nat.lt_sub_iff_add_lt', ← Nat.add_one_le_iff]
      rw [add_assoc, add_assoc]; simp only [Nat.reduceAdd]; calc
        _ ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p + ∏ p ∈ m.primeFactors, 3 := by
          nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show m≠0 by omega)]
          simp [Finsupp.prod]; apply Nat.le_self_pow
          simp; omega
        _ ≤ _ := by
          apply prod_add_prod_le
          · exact hq
          · rw [show 3 = 2+1 by rfl, ← add_assoc]
            rw [add_comm, add_assoc]; simp
            by_contra!; simp at this
            rw [Nat.factorization_eq_zero_iff] at this
            simp at hq; rcases hq with ⟨_,_,_⟩
            rcases this with h|h|h
            all_goals contradiction
          · intros; rw [add_comm, ← add_assoc]; simp
          · simp; intro p ppr _ _ _; rw [add_comm]
            apply Nat.le_add_right_of_le
            apply Nat.one_le_pow; exact ppr.pos
          all_goals simp
      simp; omega
  -- Prove that $g$ is strictly increasing on powers of prime
    have gpow : ∀ m n p, p.Prime → m < n → g (p ^ m) < g (p ^ n) := by
      intro m n p ppr mltn; have := ppr.two_le
      by_cases hm : m = 0
      · simp [hm, g1]
        apply ggt; apply Nat.one_lt_pow
        all_goals omega
      have gmgt := ggt (p ^ m) (by apply Nat.one_lt_pow; all_goals omega)
      have gngt := ggt (p ^ n) (by apply Nat.one_lt_pow; all_goals omega)
      simp [g, Finsupp.prod] at gmgt gngt
      simp [g, Finsupp.prod]
      repeat rw [ite_cond_eq_false] at *
      repeat rw [Nat.primeFactors_pow]
      simp [ppr.primeFactors, ppr.factorization_self]
      any_goals simp
      any_goals rw [pow_eq_one_iff]
      all_goals omega
  -- Prove that $g$ has the desired multiplication property
    have gmul : ∀ m > 1, ∀ n > 1, m.Coprime n → g (m * n) = g m * g n + (n + 1) * g m
    + (m + 1) * g n + m + n := by
      intro m mgt n ngt copr; simp [g, Finsupp.prod]
      have gmgt := ggt m (by omega)
      have gngt := ggt n (by omega)
      have gmulgt := ggt (m * n) (by apply one_lt_mul; all_goals omega)
      simp [g, Finsupp.prod] at gmgt gngt gmulgt
      rw [ite_cond_eq_false] at gmgt gngt gmulgt
      repeat rw [ite_cond_eq_false]
      repeat rw [Nat.sub_sub]
      zify; repeat rw [Nat.cast_sub]
      push_cast; rw [← sub_eq_zero]
      set A := ∏ x ∈ (m * n).primeFactors, (((m * n).factorization x) + x ^ (m * n).factorization x + (2 : ℤ)) with hA
      set B := ∏ x ∈ m.primeFactors, ((m.factorization x) + x ^ m.factorization x + (2 : ℤ)) with hB
      set C := ∏ x ∈ n.primeFactors, ((n.factorization x) + x ^ n.factorization x + (2 : ℤ)) with hC
      clear_value A B C; ring_nf
      rw [sub_eq_zero, hA, hB, hC]
      clear hA A hB B hC C; norm_cast
      rw [copr.primeFactors_mul, prod_union]; congr 1
      · apply prod_congr rfl
        intro p hp; rw [Nat.factorization_mul_apply_of_coprime copr]
        suffices : n.factorization p = 0
        · simp [this]
        rw [Nat.factorization_eq_zero_iff]; right; left
        have := copr.disjoint_primeFactors
        simp [disjoint_iff, Finset.ext_iff] at this
        simp at hp; intro h
        specialize this p hp.left hp.right.left hp.right.right hp.left h
        omega
      · apply prod_congr rfl
        intro p hp; rw [Nat.factorization_mul_apply_of_coprime copr]
        suffices : m.factorization p = 0
        · simp [this]
        rw [Nat.factorization_eq_zero_iff]; right; left
        rw [Nat.coprime_comm] at copr
        have := copr.disjoint_primeFactors
        simp [disjoint_iff, Finset.ext_iff] at this
        simp at hp; intro h
        specialize this p hp.left hp.right.left hp.right.right hp.left h
        omega
      exact copr.disjoint_primeFactors
      any_goals simp
      all_goals omega
    use g; split_ands
    -- Prove that $g(N)$ is the desired minimum number
    · simp [g, Finsupp.prod]
      rw [ite_cond_eq_false]
      simp; omega
    -- Prove that $g$ is positive
    · intro m mpos; by_cases hm : m = 1
      · simp [g, hm]
      specialize ggt m (by omega)
      positivity
    -- Prove that $g$ is strictly increasing on proper divisions $m ∣ n$ by apply the induction principle `Nat.recOnPrimeCoprime` on $n$
    · intro m n mltn mdvdn
      revert m; induction n using Nat.recOnPrimeCoprime with
      | h0 => simp
    -- $n$ is a power of prime, the goal follows from `gpow`
      | hp p n ppr =>
        intro m mlt mdvd
        rw [Nat.dvd_prime_pow] at mdvd
        rcases mdvd with ⟨l, llt, hl⟩
        replace llt : l < n := by
          by_contra!; replace this : l = n := by omega
          rw [this] at hl; omega
        rw [hl]; apply gpow
        all_goals assumption
    -- Prove the induction step when $n$ is product of two coprime numbers $a$ and $b$
      | h a b agt bgt copr ha hb =>
        intro m mlt mdvd
        rw [← Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime copr] at mdvd
        rw [gmul, ← mdvd]; by_cases gcda : m.gcd a = 1
      -- If $m.gcd a = 1$, then $m.gcd b < b$, we can apply `hb` to finish the goal
        · simp [gcda, add_assoc]; calc
            _ < g a * g b := by
              rw [← one_mul (g (m.gcd b))]
              apply Nat.mul_lt_mul_of_lt_of_le
              apply ggt; exact agt
              by_cases h : m.gcd b = b
              · simp [h]
              replace h : m.gcd b < b := by
                rw [Nat.lt_iff_le_and_ne]; constructor
                · apply Nat.le_of_dvd; omega
                  apply Nat.gcd_dvd_right
                exact h
              apply le_of_lt; apply hb; exact h
              apply Nat.gcd_dvd_right
              specialize ggt b bgt; positivity
            _ ≤ _ := by simp
        by_cases gcdb : m.gcd b = 1
        -- If $m.gcd b = 1$, then $m.gcd a < a$, we can apply `ha` to finish the goal
        · simp [gcdb, add_assoc]; calc
            _ < g a * g b := by
              rw [← mul_one (g (m.gcd a))]
              apply Nat.mul_lt_mul_of_le_of_lt
              by_cases h : m.gcd a = a
              · simp [h]
              replace h : m.gcd a < a := by
                rw [Nat.lt_iff_le_and_ne]; constructor
                · apply Nat.le_of_dvd; omega
                  apply Nat.gcd_dvd_right
                exact h
              apply le_of_lt; apply ha; exact h
              apply Nat.gcd_dvd_right
              apply ggt; exact bgt
              specialize ggt a agt; positivity
            _ ≤ _ := by simp
      -- If both $m.gcd a$ and $m.gcd b$ are greater than $1$, we can use `gmul` to rewrite the `LHS` and compare the terms
        rw [gmul]; simp [add_assoc]
        apply Nat.add_lt_add_of_lt_of_le
        -- Subcase when $m.gcd a = a$
        · by_cases h : m.gcd a = a
          · rw [h] at mdvd; rw [h]
            rw [← mdvd, mul_lt_mul_left] at mlt
            rw [mul_lt_mul_left]; apply hb; exact mlt
            apply Nat.gcd_dvd_right
            specialize ggt a (by omega)
            all_goals omega
          by_cases h' : m.gcd b = b
          -- Subcase when $m.gcd b = b$
          · rw [h'] at mdvd; rw [h']
            rw [← mdvd, mul_lt_mul_right] at mlt
            rw [mul_lt_mul_right]; apply ha; exact mlt
            apply Nat.gcd_dvd_right
            specialize ggt b (by omega)
            all_goals omega
        -- If $m.gcd a < a$ and $m.gcd b < b$, then we can apply `ha` and `hb` to finish the goal
          gcongr; apply ha
          · rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          · apply Nat.gcd_dvd_right
          apply hb
          rw [Nat.lt_iff_le_and_ne]; constructor
          · apply Nat.le_of_dvd; positivity
            apply Nat.gcd_dvd_right
          exact h'; apply Nat.gcd_dvd_right
        gcongr; any_goals apply Nat.gcd_le_right; positivity
        · by_cases h : m.gcd a = a
          · rw [h]
          replace h : m.gcd a < a := by
            rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          apply le_of_lt; apply ha; exact h
          apply Nat.gcd_dvd_right
        · by_cases h : m.gcd b = b
          · rw [h]
          replace h : m.gcd b < b := by
            rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          apply le_of_lt; apply hb; exact h
          apply Nat.gcd_dvd_right
        any_goals assumption
        · have : 0 < m.gcd a := by
            apply Nat.gcd_pos_of_pos_right; omega
          omega
        · have : 0 < m.gcd b := by
            apply Nat.gcd_pos_of_pos_right; omega
          omega
        have : a = a / m.gcd a * m.gcd a := by
          rw [Nat.div_mul_cancel]; apply Nat.gcd_dvd_right
        rw [this] at copr
        replace this : b = b / m.gcd b * m.gcd b := by
          rw [Nat.div_mul_cancel]; apply Nat.gcd_dvd_right
        rw [this] at copr; clear this
        rw [Nat.coprime_mul_iff_left] at copr
        nth_rw 2 [Nat.coprime_mul_iff_right] at copr
        exact copr.right.right
  -- The last goal is given by `gmul`
    exact gmul
-- On the other hand, given any such function $g$, we need to prove that $g(N)$ is at least the number given in the goal
  intro t g ht gpos hg1 hg2
  rw [ht]; clear ht t
-- Define an arithmetic function $h$ using $g$
  let h' : ZeroHom ℕ ℕ := ⟨fun k => if k ≠ 0 ∧ k ≠ 1 then g k + k + 1 else k, by simp⟩
  let h : ArithmeticFunction ℕ := h'
-- Prove that $h$ is multiplicative
  have hmul : h.IsMultiplicative := by
    constructor; simp [h, h']
    intro m n copr; by_cases hm : m ≤ 1
    · interval_cases m
      all_goals simp [h, h']
    by_cases hn : n ≤ 1
    · interval_cases n
      all_goals simp [h, h']
    simp at hm hn; simp [h, h']
    repeat rw [ite_cond_eq_true]
    rw [hg2]; ring; any_goals simp
    any_goals assumption
    all_goals omega
-- Prove that we can ditribute $h$ into any prime factorization
  have hprod : ∀ n > 1, h n = ∏ p ∈ n.primeFactors, h (p ^ n.factorization p) := by
    intro n ngt
    nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show n≠0 by omega)]
    simp [Finsupp.prod]; rw [hmul.map_prod]
    intro p hp q hq pneq; simp at hp hq
    rcases hp with ⟨_,_,_⟩; rcases hq with ⟨_,_,_⟩
    rw [Function.onFun, Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
    rw [Nat.coprime_primes]; any_goals assumption
    all_goals
    by_contra!; simp [Nat.factorization_eq_zero_iff] at this
    rcases this with _|_|_
    all_goals contradiction
-- Prove that $h (p ^ n)$ is at least $n + p ^ n + 2$ for any $n$ and prime $p$
  have hpow : ∀ n p, 1 ≤ n → p.Prime → n + p ^ n + 2 ≤ h (p ^ n) := by
    intro n p nge ppr; simp [h, h']
    have := ppr.two_le
    rw [ite_cond_eq_true]; calc
      _ = n + 1 + (p ^ n + 1) := by ring
      _ ≤ _ := by
        nth_rw 2 [add_assoc]
        simp; induction n with
        | zero => simp at nge
        | succ n ih =>
          by_cases hn : n = 0
          · simp [hn]; specialize hg1 1 p (by omega) (by simp)
            specialize gpos 1 (by simp)
            omega
          specialize ih (by omega)
          specialize hg1 (p ^ n) (p ^ (n + 1)) (by gcongr; omega; simp) (by apply pow_dvd_pow; simp)
          omega
    simp; rw [pow_eq_one_iff]
    all_goals omega
-- Use `hpow` and `hprod` to finish the goal
  calc
    _ ≤ ∏ p ∈ N.primeFactors, h (p ^ N.factorization p) := by
      apply prod_le_prod; simp
      intro p hp; simp at hp; rcases hp with ⟨_,_,_⟩
      apply hpow
      · by_contra!; simp [Nat.factorization_eq_zero_iff] at this
        rcases this with _|_|_
        all_goals contradiction
      assumption
    _ = _ := by
      rw [← hprod]; simp [h, h']
      rw [ite_cond_eq_true]; ring
      simp; all_goals omega