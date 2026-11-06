import Mathlib
/- Show that there is a unique sequence of integers $\{a_{n}\}_{n \ge 1}$ with \[a_{1}=1, \; a_{2}=2, \; a_{4}=12, \; a_{n+1}a_{n-1}=a_{n}^{2}\pm1 \;\; (n \ge 2).\] -/
def a : ℕ → ℕ
| 0 => 1
| 1 => 2
| n + 2 =>
  let an := a n
  let an1 := a (n + 1)
  2 * an1 + an
theorem algebra_73099 : ∃! a : ℕ → ℕ, a 0 = 1 ∧ a 1 = 2 ∧ a 3 = 12 ∧ (∀ n : ℕ, a (n + 2) * a n = a (n + 1) ^ 2 + 1 ∨ a (n + 2) * a n + 1 = a (n + 1) ^ 2):= by
  use a
  -- Prove that a(n+2)*a(n) - a(n+1)² = (-1)^n for all n
  have ha : ∀ n : ℕ, a (n + 2) * a n - a (n + 1) ^ 2 = (-1 : ℤ) ^ n:= by
    intro n
    induction n with
    | zero =>
      simp [a]
    | succ n ih =>
      rw [show n + 1 + 2 = n + 3 by omega]
      rw [show n + 1 + 1 = n + 2 by omega]
      have g1 : a (n + 3) = 2 * a (n + 2) + a (n + 1):= by simp [a]
      have g2 : a (n + 2) = 2 * a (n + 1) + a n:= by simp [a]
      rw [g1, g2]
      simp
      rw [g2] at ih
      simp at ih
      ring_nf at ih ⊢
      linarith
  constructor
  .
    simp
    refine ⟨by simp [a], by simp [a], by simp [a], ?_⟩

    intro n
    by_cases hn : Odd n
    .
      -- Case when n is odd: a(n+2)*a(n) + 1 = a(n+1)²
      right
      suffices a (n + 2) * a n + 1 = a (n + 1) ^ 2 by omega
      zify
      replace ha:= ha n
      rw [show (-1 : ℤ) ^ n = -1 by exact Odd.neg_one_pow hn] at ha
      linarith
    .
      -- Case when n is even: a(n+2)*a(n) = a(n+1)² + 1
      simp at hn
      left
      zify
      replace ha:= ha n
      rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow hn] at ha
      linarith
  .
    -- Prove uniqueness: any other sequence b satisfying the conditions must equal a
    intro b ⟨h1, h2, h4, h⟩
    -- First, prove that b(2) = 5
    have h3 : b 2 = 5:= by
      have g1:= h 0
      have g2:= h 1
      simp [h1, h2, h4] at g1 g2
      rcases g2 with g2 | g2
      .
        replace g2 : IsSquare 23:= by
          use b 2
          linarith
        absurd g2
        native_decide
      .
        rcases g1 with g1 | g1
        .
          exact g1
        .
          rw [g1] at g2
          norm_num at g2
    -- Prove by induction that a(n) = b(n) for all n
    have h5 : ∀ n : ℕ, a n = b n ∧ a (n + 1) = b (n + 1):= by
      intro n
      induction n with
      | zero =>
        simp [a, h1, h2]
      | succ n ih =>
        rcases ih with ⟨ih1, ih2⟩
        refine ⟨ih2, ?_⟩
        rw [show n + 1 + 1 = n + 2 by omega]
        replace ha:= ha n
        replace h:= h n
        zify at h
        replace h : ∃ e : ℤ, |e| = 1 ∧ ↑(b (n + 2)) * ↑(b n) = ↑(b (n + 1)) ^ 2 + e:= by
          rcases h with h | h
          .
            use 1
            simp
            exact h
          .
            use -1
            simp
            linarith
        rcases h with ⟨e, he, h⟩
        rw [←ih1, ←ih2] at h
        replace h : ((a (n + 2) : ℤ) - b (n + 2)) * (a n) = (-1) ^ n - e:= by linarith
        by_cases hn : n = 0 ∨ n = 1
        .
          -- Handle base cases n = 0 and n = 1
          rcases hn with rfl | rfl
          simp [a, h3]
          simp [a, h4]
        .
          -- For n ≥ 2, prove that a(n+2) = b(n+2) by contradiction
          zify
          suffices (a (n + 2) : ℤ) - b (n + 2) = 0 by linarith
          by_contra H
          replace H : |(a (n + 2) : ℤ) - b (n + 2)| > 0:= by positivity
          -- Prove that a(n) > 2 for n ≥ 2
          have h1 : ∀ n : ℕ, a (n + 2) > 2 ∧ a (n + 3) > 2:= by
            intro n
            induction n with
            | zero =>
              simp [a]
            | succ n ih =>
              rw [show n + 1 + 2 = n + 3 by omega]
              rw [show n + 1 + 3 = n + 4 by omega]
              rcases ih with ⟨ih1, ih2⟩
              refine ⟨ih2, ?_⟩
              rw [show a (n + 4) = 2 * a (n + 3) + a (n + 2) by simp [a]]
              linarith
          replace h1:= h1 (n - 2)
          rw [show n - 2 + 2 = n by omega] at h1
          replace h1:= h1.1
          replace h1 : |(a n : ℤ)| > 2:= by
            rw [abs_of_pos (by omega)]
            zify at h1
            exact h1
          replace h : |(((a (n + 2)) : ℤ)- ↑(b (n + 2))) * ↑(a n)| = |(-1) ^ n - e|:= by rw [h]
          rw [abs_mul _ _] at h
          replace H : |(a (n + 2) : ℤ) - b (n + 2)| ≥ 1:= by omega
          replace h1 : |(a n : ℤ)| ≥ 3:= by omega
          -- Prove that |(-1)^n - e| ≤ 2
          have h2 : |(-1 : ℤ) ^ n - e| ≤ 2:= by
            have h2 : |(-1 : ℤ) ^ n - e| ≤ |(-1 : ℤ) ^ n| + |e|:= by exact abs_sub ((-1) ^ n) e
            by_cases hn : Odd n
            .
              rw [show (-1 : ℤ) ^ n = -1 by exact Odd.neg_one_pow hn] at h2 ⊢
              simp at h2
              linarith
            .
              simp at hn
              rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow hn] at h2 ⊢
              simp at h2
              linarith
          replace H : |(a (n + 2) : ℤ) - b (n + 2)| * |(a n : ℤ)| ≥ 1 * 3:= by refine Int.mul_le_mul H h1 (by omega) (by omega)
          linarith
    -- Apply the induction result to prove a = b
    funext n
    replace h5:= h5 n
    rw [h5.1]
