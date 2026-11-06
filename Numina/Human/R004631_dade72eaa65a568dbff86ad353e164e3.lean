import Mathlib

/-Exercise 2. Let $\left(a_{n}\right)_{n \in \mathbb{N}}$ be a non-constant, increasing sequence of strictly positive integers such that $a_{n}$ divides $n^{2}$ for all $n \geqslant 1$. Prove that one of the following statements is true:

a) There exists an integer $n_{1}>0$ such that $a_{n}=n$ for all $n \geqslant n_{1}$.

b) There exists an integer $n_{2}>0$ such that $a_{n}=n^{2}$ for all $n \geqslant n_{2}$.-/

-- This theorem states that for a strictly increasing sequence of strictly positive integers (a_n)
-- where a_n divides n^2 for all n >= 1, one of two conditions must hold:
-- a) There exists an integer n1 > 0 such that a_n = n for all n >= n1.
-- b) There exists an integer n2 > 0 such that a_n = n^2 for all n >= n2.
theorem number_theory_291417 (a : ℕ → ℕ)
  (ha : StrictMono a) -- Assumption: a is a strictly monotone increasing sequence
  (hpos : ∀ n, 0 < a n) -- Assumption: a_n is strictly positive for all n
  (hdiv : ∀ n, 1 ≤ n → a n ∣ n ^ 2) : -- Assumption: a_n divides n^2 for all n >= 1
  (∃ n1, 0 < n1 ∧ ∀ n, n ≥ n1 → a n = n) ∨ -- Either a_n eventually becomes n
  (∃ n2, 0 < n2 ∧ ∀ n, n ≥ n2 → a n = n ^ 2) := by -- Or a_n eventually becomes n^2
  -- Human proof: "Tout d'abord, puisque pour tout entier $n$, on a $a_{n} \in \mathbb{N}^{*}$, et que la suite ( $a_{n}$ ) est croissante et non constante,
  -- il existe un entier $n_{0}$ tel que $a_{n} \geqslant 2$ pour tout $n \geqslant n_{0}$."
  -- This is established for n0=2.
  -- First, establish that a_2 >= 2.
  -- This lemma shows that a_2 is at least 2.
  have h₂ : 2 ≤ a 2 := by
    have : 0 < a 1 := hpos 1 -- a_1 > 0
    have : 1 ≤ a 1 := this -- So a_1 >= 1
    have : a 1 < a 2 := ha (by decide : 1 < 2) -- Since a is strictly monotone, a_1 < a_2
    calc -- We want to show 2 <= a_2
      2 = 1 + 1 := by decide -- 2 = 1+1
      _ ≤ a 1 + 1 := by linarith -- Since 1 <= a_1, 1+1 <= a_1+1
      _ = a 1 + 1 := rfl --
      _ ≤ a 2     := (Nat.succ_le_iff.mp this) -- Since a_1 < a_2, a_1+1 <= a_2
  -- This lemma generalizes h₂: for any n >= 2, a_n >= 2. This corresponds to n0=2 from human proof.
  have h_ge₂ : ∀ n, 2 ≤ n → 2 ≤ a n := fun n hn => h₂.trans <| ha.monotone hn -- If n >= 2, then a_n >= a_2 >= 2

  -- The proof proceeds by cases.
  -- Case 1: For all n, a_n <= n. (Human: "Supposons que, pour tout entier $n \geqslant 1$, on ait $a_{n} \leqslant n$.")
  by_cases h_case1 : ∀ n, a n ≤ n
  · -- In this case, we aim to prove that a_n = n eventually.
    -- Human proof: "Soit $p > n_{0}$ un nombre premier." (n0=2 here)
    -- Let p be a prime number such that p > 2.
    obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes 2 -- There exists a prime p such that hp₁: 2 < p and hp₂: Nat.Prime p.
    -- This lemma shows that for the chosen prime p, a_p = p.
    -- Human proof: "d'après ci-dessus, on a $a_{p}=p$." (The argument is: $a_p | p^2$, so $a_p \in \{1, p, p^2\}$.
    -- Since $p > n_0=2$, $a_p \ge 2$, so $a_p \ne 1$. Also $a_p \le p$ from h_case1. Thus $a_p=p$.)
    have ap_eq : a p = p := by
      by_contra ne -- Assume a_p != p, for contradiction.
      have lt  : a p < p   := lt_of_le_of_ne (h_case1 p) ne -- Since a_p <= p (by h_case1) and a_p != p, then a_p < p.
      have npos : 0 < a p   := hpos p -- a_p is positive.
      -- If p divides a_p, then p <= a_p (since a_p > 0). This contradicts a_p < p. So p does not divide a_p.
      have not_dvd_p : ¬ p ∣ a p := fun hpd =>
        have := Nat.le_of_dvd npos hpd; lt.not_le this
      -- Since p is prime and p does not divide a_p, p is coprime to a_p.
      have cop  := (hp₂.coprime_iff_not_dvd.mpr not_dvd_p)
      -- We know a_p divides p^2.
      have dvd2 := hdiv p (show 1 ≤ p from Nat.one_le_of_lt hp₁) -- 1 <= p because 2 < p.
      clear * - dvd2 cop hp₁ hp₂ h_ge₂ -- Clear unnecessary hypotheses for this subproof.
      -- Since p is prime and a_p divides p^2, a_p must be of the form p^k for some k <= 2.
      -- Nat.dvd_prime_pow states: a | p^N <-> a = p^k for some k <= N.
      -- So dvd2 becomes: exists k such that a_p = p^k and k <= 2.
      -- The obtain will give us this k and the equality.
      -- Let a_p = p^k. (The information k <=2 is implicitly carried).
      rw [propext (Nat.dvd_prime_pow hp₂)] at dvd2
      obtain ⟨k, hk⟩ := dvd2 -- hk is a_p = p^k.
      -- Now cop becomes: Coprime p (p^k).
      simp only [hk] at cop
      -- We want to show a contradiction. We have `cop : Coprime p (p^k)`.
      -- We will show `¬ Coprime p (p^k)`.
      revert cop; change ¬ p.Coprime (p ^ k)
      -- `¬ Coprime p (p^k)` is true if p divides p^k (since p is prime).
      refine (Nat.Prime.dvd_iff_not_coprime hp₂).mp ?_
      -- We need to show p divides p^k. This is true if k >= 1.
      refine Dvd.dvd.pow ?_ ?_
      exact Nat.dvd_refl p -- p divides p.
      -- We need to prove k >= 1. Assume k=0 for contradiction.
      by_contra hk_k_is_0; subst hk_k_is_0 -- hk_k_is_0 is k=0. Substitute k=0.
      -- If k=0, then a_p = p^0 = 1.
      simp only [zero_le, pow_zero, true_and] at hk -- This seems to simplify the equality `a_p = p^k` using `k=0`. `hk` becomes `a_p = 1`.
      -- We know p > 2 (hp₁), so p >= 2. By h_ge₂, a_p >= 2.
      have nh := h_ge₂ p hp₁
      linarith -- This derives a contradiction from a_p = 1 and a_p >= 2.
      -- Thus, the assumption k=0 was false, so k >= 1.
      -- This completes the proof that p divides p^k, which implies ¬ Coprime p (p^k).
      -- This contradicts `cop : Coprime p (p^k)`.
      -- The initial assumption `ne` (a_p != p) must be false. So a_p = p.
    -- This lemma shows by induction that a_n = n for all n >= p.
    -- Human proof: "Prouvons par récurrence que $a_{n}=n$ pour tout $n \geqslant p$."
    have rec1 : ∀ n, p ≤ n → a n = n := by
      intro n hpn -- Introduce n and the hypothesis p <= n.
      -- We use induction on n starting from p.
      induction n, hpn using Nat.le_induction with
      -- Base case: n = p. We've shown a_p = p.
      | base => exact ap_eq
      -- Inductive step: Assume a_n = n for some n >= p. Prove a_{n+1} = n+1.
      -- Human proof: "si $a_{n}=n$ pour un certain $n \geqslant p \geqslant 2$, alors $n=a_{n} \leqslant a_{n+1} \leqslant n+1$, d'où $a_{n+1}=n$ ou $a_{n+1}=n+1$."
      | succ n hpn ih => -- n is the current value, ih is a_n = n. hpn is p <= n.
        have le₁ : a n ≤ a (n + 1) := ha.monotone (Nat.le_succ n) -- a_n <= a_{n+1} by monotonicity of a.
        have le₂ : a (n+1) ≤ n+1  := h_case1 (n+1) -- a_{n+1} <= n+1 by the overall case assumption (h_case1).
        have hn_eq_an : a n = n := ih -- Inductive hypothesis: a_n = n.
        -- Using ih (a_n = n) in le₁ gives n <= a_{n+1}.
        -- Combined with le₂ (a_{n+1} <= n+1), we have n <= a_{n+1} <= n+1.
        haveI : a (n + 1) = n ∨ a (n + 1) = n + 1 := by
          rw [hn_eq_an] at le₁ -- le₁ becomes n <= a_{n+1}
          clear * - le₁ le₂ -- Keep only relevant hypotheses.
          refine Nat.le_and_le_add_one_iff.mp ⟨le₁, le₂⟩ -- n <= x <= n+1 implies x=n or x=n+1.
        -- Human proof: "Mais, $a_{n+1}$ divise $(n+1)^{2}$, tandis que $n$ ne divise pas $(n+1)^{2}$. Ainsi, on a $a_{n+1}=n+1$."
        -- We know a_{n+1} divides (n+1)^2.
        have dvd' := hdiv (n+1) (by simp only [le_add_iff_nonneg_left, zero_le]) -- Need 1 <= n+1. True for n >= p > 2.
        -- We need to show that n does not divide (n+1)^2. (n+1)^2 = n(n+2)+1.
        -- If n divides (n+1)^2, then n must divide 1, so n=1.
        -- But n >= p and p > 2, so n >= 3. Contradiction.
        have ndvd : ¬ n ∣ (n+1)^2 := fun h_n_dvd_np1_sq => by -- Assume n | (n+1)^2 for contradiction.
          clear * - h_n_dvd_np1_sq hpn hp₁ -- Keep relevant hypotheses.
          revert h_n_dvd_np1_sq; change ¬ n ∣ (n + 1) ^ 2
          have hn_ge_2 : 2 ≤ n := hp₁.trans hpn -- Since p > 2 and n >= p, we have n > 2 (so n >= 3).
          clear hp₁ hpn -- Not needed anymore.
          -- Nat.not_dvd_iff_between_consec_multiples states that if y is strictly between k*x and (k+1)*x, then x does not divide y.
          -- Here x is n, y is (n+1)^2. We need n > 0 (true as n >= 2).
          refine (Nat.not_dvd_iff_between_consec_multiples ((n + 1) ^ 2) ?_).mp ?_
          linarith -- Proof for 0 < n.
          -- We show n(n+2) < (n+1)^2 < n(n+3).
          use n + 2; constructor -- k = n+2.
          · ring_nf; simp only [add_lt_add_iff_right, lt_add_iff_pos_left, zero_lt_one] -- n^2+2n < n^2+2n+1, which is 0 < 1. True.
          · ring_nf; simp only [add_lt_add_iff_right] -- n^2+2n+1 < n^2+3n
            rw [show n * 3 = n + n * 2 by ring]; simp only [add_lt_add_iff_right]; exact hn_ge_2 -- Reduces to 1 < n, which is true as n >= 2.
        -- Now we use a_{n+1}=n or a_{n+1}=n+1.
        rcases this with han_eq_n | han_eq_np1 -- han means a_{n+1}
        · rw [han_eq_n] at dvd' -- If a_{n+1} = n, then n divides (n+1)^2.
          contradiction -- This contradicts ndvd (¬ n | (n+1)^2).
        exact han_eq_np1 -- So, a_{n+1} = n+1. This completes the induction step.
    -- Conclusion for Case 1:
    -- Human proof: "Il suffit alors de choisir $n_{1}=p$ pour conclure dans ce cas."
    left; use p; constructor -- We choose n1 = p for the first part of the theorem's OR statement.
    · exact Nat.zero_lt_of_lt hp₁ -- p > 0, since p > 2 (hp₁).
    · exact rec1 -- For all n >= p, a_n = n.
  -- Case 2: It's not true that (for all n, a_n <= n).
  -- This means there exists some m such that a_m > m.
  -- Human proof: "Supposons qu'il existe un entier $m \geqslant 1$ tel que $a_{m} > m$."
  · have ⟨m, hm⟩ := not_forall.mp h_case1 -- hm is ¬ (a_m <= m), which means m < a_m.
    -- This lemma shows by induction that for all n >= m, a_n > n.
    -- Human proof: "Une récurrence immédiate assure donc que $a_{n} > n$ pour tout $n \geqslant m$."
    have ge_strict : ∀ n, m ≤ n → a n > n := by
      intro n hmn -- Introduce n and hypothesis m <= n.
      induction n, hmn using Nat.le_induction with
      -- Base case: n = m. We have a_m > m from hm.
      | base => exact Nat.gt_of_not_le hm
      -- Inductive step: Assume a_n > n for n >= m. Prove a_{n+1} > n+1.
      -- Human proof: "On en déduit que $a_{m+1} \geqslant a_{m} > m+1$." (generalized)
      | succ n hpn ih => -- ih is a_n > n.
        haveI : n + 1 < a n + 1 := by simp only [add_lt_add_iff_right, ih] -- From a_n > n, we get a_n+1 > n+1.
        -- We want to show n+1 < a_{n+1}. We have n+1 < a_n+1.
        -- We also know a_n < a_{n+1} (strict monotonicity), so a_n+1 <= a_{n+1}.
        -- Thus, n+1 < a_n+1 <= a_{n+1}, which implies n+1 < a_{n+1}.
        apply this.trans_le; change a n < a (n + 1) -- Need to show a_n+1 <= a_{n+1}, which comes from a_n < a_{n+1}.
        exact ha (show n < n + 1 by simp only [lt_add_iff_pos_right, zero_lt_one]) -- a_n < a_{n+1} by strict monotonicity.
    -- Let B = max(m, 3). Then choose a prime p > B.
    -- This ensures p >= m (so a_p > p applies) and p >= 3 (for later arguments, e.g. p^2 > p).
    -- Human proof: "si $p \geqslant m$ est un nombre premier, on a $a_{p}=p^{2}$." (using $a_p=p$ or $a_p=p^2$ and $a_p > p$)
    let B := m ⊔ 3 -- B = max(m, 3)
    obtain ⟨p, hpB, hpP⟩ := Nat.exists_infinite_primes B -- Exists prime p such that hpB: B < p and hpP: Nat.Prime p.
    have hmB : m ≤ B := by exact Nat.le_max_left m 3 -- m <= B. So m <= B < p, which means m <= p.
    have p_ge3 : 3 ≤ p := by -- p >= 3.
      calc
        3 ≤ B := Nat.le_max_right m 3 -- 3 <= B
        _ ≤ p := hpB -- B < p implies B <= p. (Actually B <= p-1 as p, B are Nat). Thus 3 <= p.
    -- This lemma shows that for this prime p, a_p = p^2.
    -- Argument: $a_p | p^2 \implies a_p \in \{1, p, p^2\}$.
    -- Since $p \ge m$ and $p \ge 3 > n_0=2$, we have $a_p > p$.
    -- So $a_p$ must be $p^2$.
    have ap2 : a p = p ^ 2 := by
      have am_gt_m_p : a p > p := ge_strict p <| hmB.trans hpB -- Since p >= m, by ge_strict, a_p > p.
      have npos : 0 < a p := hpos p -- a_p > 0.
      have dvd2 := hdiv p (by exact Nat.one_le_of_lt p_ge3) -- a_p divides p^2 (since p >= 3 >= 1).
      by_contra ne -- Assume a_p != p^2 for contradiction.
      -- Since p is prime and a_p divides p^2, a_p = p^k for k in {0,1,2}.
      rw [propext (Nat.dvd_prime_pow hpP)] at dvd2
      obtain ⟨k, hk_le_2, hk_eq⟩ := dvd2 -- k is exponent, hk_eq is a_p = p^k, hk_le_2 is k <= 2. (Lean syntax `obtain ⟨k, hk⟩` here puts $a_p=p^k$ in hk, $k \le 2$ used implicitly by match structure).
      -- The `match k with` is on the exponent.
      match k with
      | 0 => -- Case: exponent k=0, so a_p = p^0 = 1.
        simp only [pow_zero] at hk_eq; rw [hk_eq] at am_gt_m_p -- am_gt_m_p becomes 1 > p.
        revert am_gt_m_p; change ¬ p < 1 -- This is p < 1 is false.
        simp only [Nat.lt_one_iff]; exact Nat.not_eq_zero_of_lt p_ge3 -- p < 1 means p=0. But p >= 3. Contradiction.
      | 1 => -- Case: exponent k=1, so a_p = p^1 = p.
        simp only [pow_one] at hk_eq; rw [hk_eq] at am_gt_m_p -- am_gt_m_p becomes p > p.
        simp only [gt_iff_lt, lt_self_iff_false] at am_gt_m_p -- p > p is false. Contradiction.
      | 2 => -- Case: exponent k=2, so a_p = p^2.
        simp only [hk_eq, not_true_eq_false] at ne -- hk_eq is a_p=p^2. `ne` is a_p != p^2. This makes `ne` false. Contradiction for `by_contra ne`.
      | k_val + 3 => -- Case: exponent is k_val+2 (i.e. >=2). (k_val is a new bound variable for this pattern)
                     -- Given that the exponent k <= 2, this branch is only hit if k=2 (with k_val=0).
                     -- If k=2, a_p = p^2.
        simp only [Nat.reduceLeDiff] at hk_le_2
        -- (This case seems redundant if `| 2 =>` is present, as `match` takes the first matching pattern.
        -- If k=2, it's caught by `| 2 =>`. This branch would be for k > 2, but k <= 2.)
    -- This lemma shows by induction that a_n = n^2 for all n >= p.
    -- Human proof: "Nous allons prouver par récurrence que $a_{n}=n^{2}$ pour tout $n \geqslant p$."
    have rec2 : ∀ n, p ≤ n → a n = n ^ 2 := by
      intro n hpn -- Introduce n and hypothesis p <= n.
      induction n, hpn using Nat.le_induction with
      -- Base case: n = p. We have a_p = p^2.
      | base => exact ap2
      -- Inductive step: Assume a_n = n^2 for n >= p. Prove a_{n+1} = (n+1)^2.
      -- Human proof: "Supposons que $a_{n}=n^{2}$ pour un certain entier $n \geqslant p$. Alors $n \geqslant 3$, d'où $a_{n+1} \geqslant a_{n}=n^{2} > \frac{1}{2}(n+1)^{2}$. Or, $a_{n+1}$ divise $(n+1)^{2}$, donc $a_{n+1}=(n+1)^{2}$."
      | succ n hpn ih => -- ih is a_n = n^2.
        have dvd' := hdiv (n + 1) (by simp only [le_add_iff_nonneg_left, zero_le]) -- a_{n+1} divides (n+1)^2. (Need 1 <= n+1)
        obtain ⟨q, hq⟩ := dvd' -- So (n+1)^2 = a_{n+1} * q for some integer q. We want to show q=1.
        by_cases hq_le_1 : q ≤ 1 -- Case on q.
        · -- If q <= 1: Since q must be positive (as a_{n+1} and (n+1)^2 are positive), q=1.
          -- (If n+1=0, then (n+1)^2=0, a_{n+1}*q=0. But n>=p>=3, so n+1 > 0).
          match q with
          | 0 => simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false] at hq -- If q=0, (n+1)^2 = 0, so n+1=0. Impossible.
          | 1 => simp only [mul_one] at hq; simp only [hq] -- If q=1, (n+1)^2 = a_{n+1}. This is the goal.
        -- If not (q <= 1), then q > 1, so q >= 2.
        simp only [not_le] at hq_le_1 -- hq_le_1 is now q >= 2.
        have an_lt_anp1 := ha (show n < n + 1 by simp only [lt_add_iff_pos_right, zero_lt_one]) -- a_n < a_{n+1} by strict monotonicity.
        rw [ih] at an_lt_anp1; clear ih -- So n^2 < a_{n+1}.
        have n_ge_p_ge_3 := p_ge3.trans hpn; clear * - n_ge_p_ge_3 hq hq_le_1 an_lt_anp1 -- Keep only relevant hypotheses. n_ge_p_ge_3 means n >= p >= 3.
        -- The human proof argues $n^2 > \frac{1}{2}(n+1)^2$ for $n \ge 3$. This means $2n^2 > (n+1)^2$.
        -- Since $a_{n+1} > n^2$, it implies $a_{n+1} > \frac{1}{2}(n+1)^2$.
        -- Since $a_{n+1} | (n+1)^2$, this forces $a_{n+1} = (n+1)^2$, so $q=1$.
        -- The Lean proof shows a contradiction if q >= 2 by showing $2n^2 < (n+1)^2$, which is $n^2 - 2n - 1 < 0$.
        -- This is false for $n \ge 3$. (True for $n=1,2$. $n=0$ gives $-1 < 0$. $n=1$ gives $-2<0$. $n=2$ gives $-1<0$. $n=3$ gives $2>0$).
        -- We want to show $2n^2 < a_{n+1} \cdot q$.
        haveI : 2 * n ^ 2 < a (n + 1) * q := by
          -- We show $2 \cdot n^2 < a_{n+1} \cdot 2 \le a_{n+1} \cdot q$.
          apply @LT.lt.trans_le _ _ _ (a (n + 1) * 2) -- Transitivity step.
          · -- Show $2 \cdot n^2 < a_{n+1} \cdot 2$. This is $n^2 < a_{n+1}$ (since $2>0$).
            rw [mul_comm] -- $n^2 \cdot 2 < a_{n+1} \cdot 2$.
            refine Nat.mul_lt_mul_of_pos_right an_lt_anp1 ?_; decide -- an_lt_anp1 is $n^2 < a_{n+1}$. Second arg is $0 < 2$.
          · -- Show $a_{n+1} \cdot 2 \le a_{n+1} \cdot q$. This holds if $2 \le q$ (which is hq_le_1) and $a_{n+1} > 0$.
            exact Nat.mul_le_mul_left (a (n + 1)) hq_le_1 -- a_{n+1} is positive (from hpos).
        rw [← hq] at this; ring_nf at this -- Substitute $(n+1)^2 = a_{n+1} \cdot q$. So $2n^2 < (n+1)^2$. This simplifies to $n^2 < 2n+1$.
        rw [mul_two] at this; simp only [add_lt_add_iff_right] at this -- this is $n^2 < 1 + n \cdot 2$.
        exfalso; revert this; change ¬ n ^ 2 < 1 + n * 2 -- We want to prove this is false, i.e., $n^2 \ge 1+2n$.
        simp only [not_lt] -- Goal: $1 + n \cdot 2 \le n^2$.
        clear * - n_ge_p_ge_3 -- We only need n >= 3.
        -- We need to show $1+2n \le n^2$ for $n \ge 3$.
        -- $n^2 - 2n - 1 \ge 0$. Roots are $1 \pm \sqrt{2}$. So true for $n \ge 1+\sqrt{2} \approx 2.414$. Thus for $n \ge 3$.
        haveI : 1 + n * 2 ≤ n * 3 := by linarith -- $1+2n \le 3n \iff 1 \le n$. True since $n \ge 3$.
        apply this.trans -- So we need to show $n \cdot 3 \le n^2$.
        rw [pow_two]; exact Nat.mul_le_mul_left n n_ge_p_ge_3 -- $3n \le n^2 \iff 3 \le n$ (if $n>0$). True as $n \ge 3$.
        -- This provides the contradiction for $q \ge 2$.
        -- So the case q >= 2 is impossible.
    -- Conclusion for Case 2:
    -- Human proof: "Il suffit donc de choisir $\mathrm{n}_{2}=\mathrm{p}$ pour conclure dans ce cas."
    right; use p; constructor; -- We choose n2 = p for the second part of the theorem's OR statement.
    exact Nat.zero_lt_of_lt p_ge3 -- p > 0, since p >= 3 (p_ge3).
    exact rec2 -- For all n >= p, a_n = n^2.
