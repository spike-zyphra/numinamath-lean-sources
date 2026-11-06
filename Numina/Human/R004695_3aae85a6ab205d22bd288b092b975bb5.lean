import Mathlib
/- 5. Let $k$ be an integer greater than 1, and the sequence $\left\{a_{n}\right\}$ is defined as follows:
$$
\begin{array}{l}
a_{0}=0, a_{1}=1, \\
a_{n+1}=k a_{n}+a_{n-1}(n=1,2, \cdots) .
\end{array}
$$

Find all $k$ that satisfy the following condition: there exist non-negative integers $l, m (l \neq m)$, and positive integers $p, q$, such that
$a_{l}+k a_{0}=a_{m}+k a_{q^{*}} \quad$ (Xiong Bin) -/
def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an := a n
  let an1 := a (n + 1)
  2 * an1 + an
theorem algebra_304098 : {k : ℕ | k > 1 ∧ (∃ a : ℕ → ℕ, a 0 = 0 ∧ a 1 = 1 ∧ (∀ n : ℕ, a (n + 2) = k * a (n + 1) + a n) ∧ (∃ l m p q : ℕ, l ≠ m ∧ p > 0 ∧ q > 0 ∧ a l + k * a p = a m + k * a q))} = {2}:= by
  ext k
  constructor
  .
    -- Forward direction: if k satisfies the condition, then k=2
    intro h
    simp at h
    rcases h with ⟨hk, h1⟩
    rcases h1 with ⟨a, h1, h2, hn, h⟩
    rcases h with ⟨l, m, hlm, ⟨p, hp, q, hq, h⟩⟩

    -- Prove that a(n+1) > 0 for all n
    have g1 : ∀ n : ℕ, a (n + 1) > 0:= by
      intro n
      induction n with
      | zero =>
        simp [h2]
      | succ n ih =>
        rw [hn n]
        positivity

    -- Prove that a(n+1) > a(n) for all n (sequence is strictly increasing)
    have g2 : ∀ n : ℕ, a (n + 1) > a n:= by
      intro n
      induction n with
      | zero =>
        simp [h1, h2]
      | succ n ih =>
        rw [hn n]
        replace hk : k ≥ 2:= by omega
        replace hk : k * a (n + 1) ≥ 2 * a (n + 1):= by exact Nat.mul_le_mul_right (a (n + 1)) hk
        linarith

    -- Extend the increasing property: a(n+m+1) > a(n) for all n, m
    replace g2 : ∀ n : ℕ, ∀ m : ℕ, a (n + m + 1) > a n:= by
      intro n m
      induction m with
      | zero =>
        simp [g2 n]
      | succ m ih =>
        rw [show n + (m + 1) + 1 = n + m + 1 + 1 by omega]
        linarith [g2 (n + m + 1)]

    -- Prove that a(n+2) ≡ a(n) (mod k)
    have g3 : ∀ n : ℕ, a (n + 2) ≡ a n [MOD k]:= by
      intro n
      rw [hn n]
      have g : k * a (n + 1) + a n ≥ a n:= by omega
      suffices k ∣ k * a (n + 1) + a n - a n by exact Nat.ModEq.symm ((Nat.modEq_iff_dvd' g).mpr this)
      use a (n + 1)
      omega

    -- Prove that a(2n) ≡ 0 (mod k) for all n
    have g4 : ∀ n : ℕ, a (2 * n) ≡ 0 [MOD k]:= by
      intro n
      induction n with
      | zero =>
        simp [h1]
        rfl
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        replace g3:= g3 (2 * n)
        exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm ih)) (id (Nat.ModEq.symm g3)))

    -- Prove that a(2n+1) ≡ 1 (mod k) for all n
    have g5 : ∀ n : ℕ, a (2 * n + 1) ≡ 1 [MOD k]:= by
      intro n
      induction n with
      | zero =>
        simp [h2]
        rfl
      | succ n ih =>
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
        replace g3:= g3 (2 * n + 1)
        exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm ih)) (id (Nat.ModEq.symm g3)))

    -- Prove that a(n+1) ≢ a(n) (mod k) for all n
    replace g3 : ∀ n : ℕ, ¬(a (n + 1) ≡ a n [MOD k]):= by
      intro n
      by_contra H
      by_cases g : Even n
      .
        -- Case: n is even
        rcases g with ⟨t, ht⟩
        rw [show t + t = 2 * t by omega] at ht
        subst n
        replace g4:= g4 t
        replace g5:= g5 t
        replace H : a (2 * t + 1) ≡ 0 [MOD k]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g4)) (id (Nat.ModEq.symm H)))
        replace H : 1 ≡ 0 [MOD k]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm H)) g5)
        simp [Nat.ModEq] at H
        omega
      .
        -- Case: n is odd
        simp at g
        rcases g with ⟨t, rfl⟩
        rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega] at H
        replace g4:= g4 (t + 1)
        replace g5:= g5 t
        replace H : a (2 * (t + 1)) ≡ 1 [MOD k]:= by exact Nat.ModEq.trans H g5
        replace H : 0 ≡ 1 [MOD k]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm g4)) H
        simp [Nat.ModEq] at H
        omega

    clear g4 g5

    -- Prove that if a(n) ≤ a(m), then n ≤ m (monotonicity)
    have g4 : ∀ n m : ℕ, a n ≤ a m → n ≤ m:= by
      intro n m h
      by_contra H
      simp at H
      replace g2:= g2 m (n - (m + 1))
      rw [show m + (n - (m + 1)) + 1 = n by omega] at g2
      linarith

    -- Prove that if n ≤ m, then a(n) ≤ a(m) (monotonicity)
    have g5 : ∀ n m : ℕ, n ≤ m → a n ≤ a m:= by
      intro n m h
      by_cases h1 : n = m
      .
        subst n
        simp
      .
        replace h : n < m:= by omega
        replace g2:= g2 n (m - (n + 1))
        rw [show n + (m - (n + 1)) + 1 = m by omega] at g2
        linarith

    -- Main lemma: if l < m, p > 0, q > 0, and a(l) + k*a(p) = a(m) + k*a(q), then k = 2
    have g : ∀ l m p q: ℕ, l < m → p > 0 → q > 0 → a l + k * a p = a m + k * a q → k = 2:= by
      intro l m p q hlm hp hq h

      -- Prove that m ≥ l + 2
      replace hlm : m ≥ l + 2:= by
        by_contra H
        replace H : m = l + 1:= by omega
        replace h : a m ≡ a l [MOD k]:= by
          have H1 : k * a p ≡ 0 [MOD k]:= by
            suffices k ∣ k * a p by exact Nat.modEq_zero_iff_dvd.mpr this
            simp
          have H2 : k * a q ≡ 0 [MOD k]:= by
            suffices k ∣ k * a q by exact Nat.modEq_zero_iff_dvd.mpr this
            simp
          replace H1 : a l + k * a p ≡ a l + 0 [MOD k]:= by exact Nat.ModEq.add_left (a l) H1
          replace H2 : a m + k * a q ≡ a m + 0 [MOD k]:= by exact Nat.ModEq.add_left (a m) H2
          rw [h] at H1
          simp at H1 H2
          exact Nat.ModEq.trans (id (Nat.ModEq.symm H2)) H1
        subst m
        replace g3:= g3 l
        trivial

      -- Prove that l < p
      have h3 : l < p:= by
        by_contra H
        have H0:= H
        simp at H
        replace H : a p ≤ a l:= by exact g5 p l H
        replace hlm : a m ≥ a (l + 2):= by exact g5 (l + 2) m hlm
        rw [hn l] at hlm
        replace hlm : k * a p ≥ k * a (l + 1):= by omega
        replace hlm : a p ≥ a (l + 1):= by
          replace hk : k > 0:= by omega
          exact Nat.le_of_mul_le_mul_left hlm hk
        replace g2:= g2 p (l - p)
        rw [show p + (l - p) + 1 = l + 1 by omega] at g2
        linarith

      -- Prove that a(m) ≤ a(p+1)
      have h4 : a m ≤ a (p + 1):= by
        suffices a m + k * a q ≤ a (p + 1) by omega
        rw [←h]
        replace hn:= hn (p - 1)
        rw [show p - 1 + 2 = p + 1 by omega] at hn
        rw [show p - 1 + 1 = p by omega] at hn
        replace g5:= g5 l (p - 1) (by omega)
        linarith

      -- Prove that m ≤ p
      replace h4:= g4 m (p + 1) h4
      replace h4 : m ≤ p:= by
        by_contra H
        replace H : m = p + 1:= by omega
        subst m
        replace hn:= hn (p - 1)
        rw [show p - 1 + 2 = p + 1 by omega] at hn
        rw [show p - 1 + 1 = p by omega] at hn
        replace g5:= g5 l (p - 1) (by omega)
        rw [hn] at h
        replace h : k * a q = 0:= by omega
        replace g1:= g1 (q - 1)
        rw [show q - 1 + 1 = q by omega] at g1
        replace g1 : k * a q > 0:= by positivity
        linarith

      -- Prove that a(q) ≥ a(p-1)
      have h5 : a q ≥ a (p - 1):= by
        suffices q ≥ p - 1 by exact g5 (p - 1) q this
        by_contra H
        simp at H
        have g:= hn (p - 2)
        rw [show p - 2 + 2 = p by omega] at g
        rw [show p - 2 + 1 = p - 1 by omega] at g
        replace g : k * a (p - 1) < a p:= by
          replace g1:= g1 (p - 3)
          rw [show p - 3 + 1 = p - 2 by omega] at g1
          linarith
        have g6:= g5 q (p - 1) (by omega)
        replace g6 : k * a q ≤ k * a (p - 1):= by exact Nat.mul_le_mul_left k g6
        have g7:= g5 m p h4
        replace hk : k ≥ 2:= by omega
        replace hk : k * a p ≥ 2 * a p:= by exact Nat.mul_le_mul_right (a p) hk
        linarith

      -- Prove that q = p - 1
      replace h5 : q = p - 1:= by
        replace h5:= g4 (p - 1) q h5
        by_contra H
        replace H : q ≥ p:= by omega
        replace H:= g5 p q H
        replace H:= Nat.mul_le_mul_left k H
        replace g2:= g2 l (m - (l + 1))
        rw [show l + (m - (l + 1)) + 1 = m by omega] at g2
        linarith

      subst q

      -- Prove that m = p
      replace h4 : m = p:= by
        by_contra H
        replace h4 : m < p:= by omega
        have g6:= g2 m (p - (m + 1))
        rw [show m + (p - (m + 1)) + 1 = p by omega] at g6
        replace hn:= hn (p - 2)
        rw [show p - 2 + 2 = p by omega] at hn
        rw [show p - 2 + 1 = p - 1 by omega] at hn
        replace g1:= g1 (p - 3)
        rw [show p - 3 + 1 = p - 2 by omega] at g1
        replace hk : k ≥ 2:= by omega
        replace hk : k * a p ≥ 2 * a p:= by exact Nat.mul_le_mul_right (a p) hk
        linarith

      subst m

      -- Prove that p = 2
      have h4 : p = 2:= by
        by_contra H
        replace hn:= hn (p - 2)
        rw [show p - 2 + 2 = p by omega] at hn
        rw [show p - 2 + 1 = p - 1 by omega] at hn
        replace g1:= g1 (p - 3)
        rw [show p - 3 + 1 = p - 2 by omega] at g1
        replace hk : k ≥ 2:= by omega
        replace hk : k * a p ≥ 2 * a p:= by exact Nat.mul_le_mul_right (a p) hk
        linarith

      subst p

      -- Substitute the values and solve for k
      rw [hn 0] at h
      simp [h1, h2] at h
      simp at hlm
      subst l
      simp [h1] at h
      ring_nf at h
      rw [show k ^ 2 = k * k by ring] at h
      replace hk : k > 0:= by omega
      nlinarith only [hk, h]

    -- Handle the case where l ≠ m (either l < m or l > m)
    replace hlm : l < m ∨ l > m:= by omega
    simp
    rcases hlm with hlm | hlm
    .
      -- Case: l < m
      exact g l m p q hlm hp hq h
    .
      -- Case: l > m (swap the roles)
      exact g m l q p hlm hq hp (by linarith)
  .
    -- Backward direction: if k = 2, then k satisfies the condition
    intro h
    simp at h
    subst k
    simp
    use a
    simp [a]
    use 0, 2
    simp
    use 2
    simp
    use 1
    simp [a]
