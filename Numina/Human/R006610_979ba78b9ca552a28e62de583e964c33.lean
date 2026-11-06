import Mathlib
/- Let $N_0$ be a positive integer. Let $N = 4N_0$. Let $b=7$ and $d=8$.
Set $A=\sum_{k=1}^{N} \lfloor \frac{b^k}{d} \rfloor$.
Determine the remainder when $A$ is divided by 50. Show that this remainder is equal to $(-2N_639132 \bmod 50)$, where $(x \bmod m)$ denotes the unique remainder $r$ such that $x \equiv r \pmod m$ and $0 \le r < m$. -/
theorem number_theory_639132 (n : ℕ) (hn : n > 0) : (∑ i in Finset.range (4 * n), (7 : ℤ) ^ (i + 1) / 8) ≡ -2 * n [ZMOD 50]:= by
  -- Lemma 1: 7^(2k) ≡ 1 (mod 8) for any natural number k
  have h1 : ∀ k : ℕ, 7 ^ (2 * k) ≡ 1 [MOD 8]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      rw [show 7 ^ (2 * k + 2) = 7 ^ (2 * k) * 7 ^ 2 by ring]
      simp
      replace ih : 7 ^ (2 * k) * 49 ≡ 1 * 49 [MOD 8]:= by exact Nat.ModEq.mul ih rfl
      simp at ih
      exact ih
  -- Lemma 2: 7^(2k+1) ≡ 7 (mod 8) for any natural number k
  have h2 : ∀ k : ℕ, 7 ^ (2 * k + 1) ≡ 7 [MOD 8]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega]
      rw [show 7 ^ (2 * k + 1 + 2) = 7 ^ (2 * k + 1) * 7 ^ 2 by ring]
      simp
      replace ih : 7 ^ (2 * k + 1) * 49 ≡ 7 * 49 [MOD 8]:= by exact Nat.ModEq.mul ih rfl
      simp at ih
      exact ih
  -- Lemma 3: For any k, floor(7^(2k+2)/8) + floor(7^(2k+1)/8) = 7^(2k+1) - 1
  have h3 : ∀ k : ℕ, 7 ^ (2 * k + 2) / 8 + 7 ^ (2 * k + 1) / 8 = 7 ^ (2 * k + 1) - 1:= by
    intro k
    specialize h1 (k + 1)
    specialize h2 k
    rw [show 2 * (k + 1) = 2 * k + 2 by omega] at h1
    have g1 : 7 ^ (2 * k + 2) = 8 * (7 ^ (2 * k + 2) / 8) + 7 ^ (2 * k + 2) % 8:= by omega
    have g2 : 7 ^ (2 * k + 1) = 8 * (7 ^ (2 * k + 1) / 8) + 7 ^ (2 * k + 1) % 8:= by omega
    rw [h1] at g1
    rw [h2] at g2
    simp at g1 g2
    rw [show 7 ^ (2 * k + 2) = 7 * 7 ^ (2 * k + 1) by ring_nf] at g1 ⊢
    omega
  -- Convert the previous lemma to work with integers
  replace h3 : ∀ k : ℕ, (7 : ℤ) ^ (2 * k + 2) / 8 + 7 ^ (2 * k + 1) / 8 = 7 ^ (2 * k + 1) - 1:= by
    intro k
    specialize h3 k
    zify at h3
    simp at h3
    exact h3
  -- Main induction: Prove the theorem by induction on n
  have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range (4 * n), 7 ^ (i + 1) / 8 ≡ -2 * ↑n [ZMOD 50]:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      -- Expand the sum for n+1 by adding 4 more terms
      rw [show 4 * (n + 1) = 4 * n + 4 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      -- Rewrite the new indices in terms of 2k+1 and 2k+2 patterns
      rw [show 4 * n + 3 + 1 = 2 * (2 * n + 1) + 2 by omega]
      rw [show 4 * n + 2 + 1 = 2 * (2 * n + 1) + 1 by omega]
      rw [show 4 * n + 1 + 1 = 2 * (2 * n) + 2 by omega]
      rw [show 4 * n + 1 = 2 * (2 * n) + 1 by omega]
      simp
      -- Apply the key lemma to combine pairs of terms
      have g1:= h3 (2 * n)
      have g2:= h3 (2 * n + 1)
      rw [show ∑ x ∈ Finset.range (4 * n), (7 : ℤ) ^ (x + 1) / 8 + 7 ^ (2 * (2 * n) + 1) / 8 + 7 ^ (2 * (2 * n) + 2) / 8 + 7 ^ (2 * (2 * n + 1) + 1) / 8 + 7 ^ (2 * (2 * n + 1) + 2) / 8  = ∑ x ∈ Finset.range (4 * n), 7 ^ (x + 1) / 8 + ((7 ^ (2 * (2 * n) + 2) / 8 + 7 ^ (2 * (2 * n) + 1) / 8) + (7 ^ (2 * (2 * n + 1) + 2) / 8 + 7 ^ (2 * (2 * n + 1) + 1) / 8)) by ring]
      rw [g1, g2]
      -- Rewrite powers of 7 in terms of 49 = 7^2
      rw [show (7 : ℤ) ^ (2 * (2 * n) + 1) = 7 * 7 ^ (2 * (2 * n)) by ring_nf]
      rw [show (7 : ℤ) ^ (2 * (2 * n + 1) + 1) = 7 * 7 ^ (2 * (2 * n + 1)) by ring_nf]
      clear g1 g2
      rw [show (7 : ℤ) ^ (2 * (2 * n)) = (7 ^ 2) ^ (2 * n) by exact pow_mul 7 2 (2 * n)]
      rw [show (7 : ℤ) ^ (2 * (2 * n + 1)) = (7 ^ 2) ^ (2 * n + 1) by exact pow_mul 7 2 (2 * n + 1)]
      simp
      -- Use the fact that 49 ≡ -1 (mod 50) to simplify the expression
      have g1 : 49 ≡ -1 [ZMOD 50]:= by rfl
      have g2:= Int.ModEq.pow (2 * n + 1) g1
      replace g1:= Int.ModEq.pow (2 * n) g1
      simp at g1
      rw [show (-1) ^ (2 * n + 1) = -1 by exact Odd.neg_one_pow (by norm_num)] at g2
      replace g2 : 7 * 49 ^ (2 * n + 1) ≡ 7 * (-1) [ZMOD 50]:= by exact Int.ModEq.mul_left 7 g2
      replace g1 : 7 * 49 ^ (2 * n) ≡ 7 * 1 [ZMOD 50]:= by exact Int.ModEq.mul_left 7 g1
      simp at g1 g2
      -- Combine the terms and use the induction hypothesis
      rw [show (7 : ℤ) * 49 ^ (2 * n) - 1 + (7 * 49 ^ (2 * n + 1) - 1) = 7 * 49 ^ (2 * n) + 7 * 49 ^ (2 * n + 1) + -2 by ring]
      replace g1:= Int.ModEq.add g1 g2
      simp at g1
      replace g1 : 7 * 49 ^ (2 * n) + 7 * 49 ^ (2 * n + 1) + -2 ≡ 0 + -2 [ZMOD 50]:= by exact Int.ModEq.add g1 rfl
      replace g1:= Int.ModEq.add ih g1
      simp at g1
      rw [show -(2 * (↑n : ℤ)) + -2 = -(2 * (n + 1)) by ring] at g1
      exact g1
  -- Apply the main result to the input n
  exact h4 n
