import Mathlib
/- Let $Y$ be a positive even integer that is not divisible by 7.
Let $m = 2^{1980} \cdot 3^{384} \cdot 5^Y \cdot 7^{343}$.
Let $n$ be the smallest positive integer such that $mn$ is a perfect $k$-th power of an integer for some integer $k \ge 2$.
Determine the value of $n+k$. Show the answer is 9. -/
theorem number_theory_639253 (y m : ℕ) (hy : y > 0) (hy1 : Even y) (hy2 : ¬(7 ∣ y)) (hm : m = 2 ^ 1980 * 3 ^ 384 * 5 ^ y * 7 ^ 343) : IsLeast {S : ℕ | ∃ n k p : ℕ, n > 0 ∧ k ≥ 2 ∧ n * m = p ^ k ∧ S = n + k} 9:= by
  -- Define constants for the exponents to simplify the proof
  set a1:= 990 with ha1
  set a2:= 192 with ha2
  set a3:= 171 with ha3
  clear_value a1 a2 a3
  -- Rewrite the exponents in terms of the defined constants
  rw [show 1980 = 2 * a1 by linarith] at hm
  rw [show 384 = 2 * a2 by linarith] at hm
  rw [show 343 = 2 * a3 + 1 by linarith] at hm
  -- Use the fact that y is even to write y = 2*y' for some y'
  rcases hy1 with ⟨y, rfl⟩
  simp at hy
  constructor
  .
    -- First part: Show that 9 is in the set (i.e., there exists n=7, k=2 such that 7*m is a perfect square)
    simp
    use 7
    simp
    use 2
    simp
    use 2 ^ a1 * 3 ^ a2 * 5 ^ y * 7 ^ (a3 + 1)
    subst m
    ring_nf
  .
    -- Second part: Show that 9 is the least element (i.e., any element in the set is ≥ 9)
    simp [lowerBounds]
    intro S n hn k hk p hp hS
    subst S
    -- Key lemma: If a product of prime powers is a perfect k-th power, then k divides all exponents
    have h1 : ∀ a1 a2 a3 a4 : ℕ, ∀ k : ℕ, k ≥ 2 → (∃ p : ℕ, 2 ^ a1 * 3 ^ a2 * 5 ^ a3 * 7 ^ a4 = p ^ k) → (k ∣ a1 ∧ k ∣ a2 ∧ k ∣ a3 ∧ k ∣ a4):= by
      intro a1 a2 a3 a4 k hk hp
      -- Show that 7^a4 is coprime with the product of other prime powers
      have g1 : Nat.Coprime 7 2:= by norm_num
      have g2 : Nat.Coprime 7 3:= by norm_num
      have g3 : Nat.Coprime 7 5:= by norm_num
      replace g1 : Nat.Coprime (7 ^ a4) (2 ^ a1):= by exact Nat.Coprime.pow a4 a1 g1
      replace g2 : Nat.Coprime (7 ^ a4) (3 ^ a2):= by exact Nat.Coprime.pow a4 a2 g2
      replace g3 : Nat.Coprime (7 ^ a4) (5 ^ a3):= by exact Nat.Coprime.pow a4 a3 g3
      replace g1:= Nat.Coprime.mul_right g1 g2
      replace g1:= Nat.Coprime.mul_right g1 g3
      rcases hp with ⟨p, hp⟩
      -- Use the fact that coprime factors of a perfect power must themselves be perfect powers
      have g4:= exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr g1) (show 7 ^ a4 * (2 ^ a1 * 3 ^ a2 * 5 ^ a3) = p ^ k by linarith)
      replace g1:= Nat.coprime_comm.mp g1
      replace g1:= Nat.isUnit_iff.mpr g1
      replace g1:= exists_eq_pow_of_mul_eq_pow g1 hp
      -- Lemma: If p^n is a perfect k-th power, then k divides n
      have g : ∀ p n : ℕ, Nat.Prime p → (∃ d, p ^ n = d ^ k) → k ∣ n:= by
        intro p n g g4
        rcases g4 with ⟨d, hd⟩
        have g4 : d ∣ p ^ n:= by
          use d ^ (k - 1)
          rw [show d * d ^ (k - 1) = d ^ (1 + (k - 1)) by ring]
          rw [show 1 + (k - 1) = k by omega]
          exact hd
        replace g4 : ∃ t : ℕ, t ≤ n ∧ d = p ^ t:= by exact (Nat.dvd_prime_pow g).mp g4
        rcases g4 with ⟨t, -, ht2⟩
        subst d
        ring_nf at hd
        replace hd : Nat.log p (p ^ n) = Nat.log p (p ^ (t * k)):= by rw [hd]
        have g0 : p > 1:= by exact Nat.Prime.one_lt g
        rw [Nat.log_pow (by omega) _] at hd
        rw [Nat.log_pow (by omega) _] at hd
        use t
        linarith
      -- Apply the lemma to show k divides the exponent of 7
      replace g4:= g 7 a4 (by norm_num) g4
      -- Show that 5^a3 is coprime with the product of 2^a1 and 3^a2
      replace g2 : Nat.Coprime 5 2:= by norm_num
      replace g3 : Nat.Coprime 5 3:= by norm_num
      replace g2 : Nat.Coprime (5 ^ a3) (2 ^ a1):= by exact Nat.Coprime.pow a3 a1 g2
      replace g3 : Nat.Coprime (5 ^ a3) (3 ^ a2):= by exact Nat.Coprime.pow a3 a2 g3
      replace g2:= Nat.Coprime.mul_right g2 g3
      clear hp p
      rcases g1 with ⟨p, hp⟩
      have g1:= exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr g2) (show 5 ^ a3 * (2 ^ a1 * 3 ^ a2) = p ^ k by linarith)
      replace g2:= Nat.coprime_comm.mp g2
      replace g2:= Nat.isUnit_iff.mpr g2
      replace g2:= exists_eq_pow_of_mul_eq_pow g2 hp
      -- Show that 2^a1 and 3^a2 are coprime
      replace g3 : Nat.Coprime 2 3:= by norm_num
      replace g3 : Nat.Coprime (2 ^ a1) (3 ^ a2):= by exact Nat.Coprime.pow a1 a2 g3
      clear hp p
      rcases g2 with ⟨p, hp⟩
      have g5:= exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr g3) hp
      replace g3:= Nat.coprime_comm.mp g3
      replace g3:= exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr g3) (show 3 ^ a2 * 2 ^ a1 = p ^ k by linarith)
      -- Apply the lemma to show k divides all exponents
      replace g1:= g 5 a3 (by norm_num) g1
      replace g3:= g 3 a2 (by norm_num) g3
      replace g5:= g 2 a1 (by norm_num) g5
      exact ⟨g5, g3, g1, g4⟩
    -- Proof by contradiction: assume n+k < 9
    by_contra H
    -- Since n+k < 9 and n > 0, k ≥ 2, we must have n ≤ 6
    have H1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6:= by omega
    rw [show y + y = 2 * y by omega] at hm
    -- Case analysis on n from 1 to 6
    rcases H1 with H1 | H1 | H1 | H1 | H1 | H1
    all_goals
      subst n m
    .
      -- Case n = 1: Check if m itself is a perfect k-th power
      simp at hp
      replace h1:= h1 (2 * a1) (2 * a2) (2 * y) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      -- Since k must divide all exponents, check possible values of k
      replace H : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7:= by omega
      rcases H with H | H | H | H | H | H
      all_goals
        subst k
        omega
    .
      -- Case n = 2: Check if 2*m is a perfect k-th power
      rw [show 2 * (2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1)) = 2 ^ (2 * a1 + 1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1) by ring_nf] at hp
      replace h1:= h1 (2 * a1 + 1) (2 * a2) (2 * y) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      replace H : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6:= by omega
      rcases H with H | H | H | H | H
      all_goals
        subst k
        omega
    .
      -- Case n = 3: Check if 3*m is a perfect k-th power
      rw [show 3 * (2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1)) = 2 ^ (2 * a1) * 3 ^ (2 * a2 + 1) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1) by ring_nf] at hp
      replace h1:= h1 (2 * a1) (2 * a2 + 1) (2 * y) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      replace H : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5:= by omega
      rcases H with H | H | H | H
      all_goals
        subst k
        omega
    .
      -- Case n = 4: Check if 4*m is a perfect k-th power
      rw [show 4 * (2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1)) = 2 ^ (2 * a1 + 2) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1) by ring_nf] at hp
      replace h1:= h1 (2 * a1 + 2) (2 * a2) (2 * y) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      replace H : k = 2 ∨ k = 3 ∨ k = 4:= by omega
      rcases H with H | H | H
      all_goals
        subst k
        omega
    .
      -- Case n = 5: Check if 5*m is a perfect k-th power
      rw [show 5 * (2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1)) = 2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y + 1) * 7 ^ (2 * a3 + 1) by ring_nf] at hp
      replace h1:= h1 (2 * a1) (2 * a2) (2 * y + 1) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      replace H : k = 2 ∨ k = 3:= by omega
      rcases H with H | H
      all_goals
        subst k
        omega
    .
      -- Case n = 6: Check if 6*m is a perfect k-th power
      rw [show 6 * (2 ^ (2 * a1) * 3 ^ (2 * a2) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1)) = 2 ^ (2 * a1 + 1) * 3 ^ (2 * a2 + 1) * 5 ^ (2 * y) * 7 ^ (2 * a3 + 1) by ring_nf] at hp
      replace h1:= h1 (2 * a1 + 1) (2 * a2 + 1) (2 * y) (2 * a3 + 1) k hk ⟨p, hp⟩
      rw [ha1, ha2, ha3] at h1
      replace H : k = 2:= by omega
      subst k
      omega
