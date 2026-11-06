import Mathlib
/- Let $k$ be an odd positive integer. Prove that $\lfloor (2+\sqrt{5})^k \rfloor$ is not prime. -/
theorem number_theory_641227 (k : ℕ) (hk : Odd k) : ¬Prime ⌊(2 + √5) ^ k⌋:= by
  -- Define key variables: a = 2 + √5, b = 2 - √5
  -- Define sequence c(n) = a^n + b^n
  set a:= 2 + √5 with ha
  set b:= 2 - √5 with hb
  set c : ℕ → ℝ:= fun n => a ^ n + b ^ n with hc
  clear_value a b c

  -- Prove that both a and b satisfy the quadratic equation x^2 = 4x + 1
  have h1 : ∀ x : ℝ, x = a ∨ x = b → x ^ 2 = 4 * x + 1:= by
    intro x hx
    rcases hx with hx | hx
    all_goals
      subst x a b
      ring_nf
      field_simp
      ring_nf
  have h2:= h1 b (by simp)
  replace h1:= h1 a (by simp)

  -- Prove that sequence c satisfies recurrence relation: c(n+2) = 4c(n+1) + c(n)
  have h3 : ∀ n : ℕ, c (n + 2) = 4 * c (n + 1) + c n:= by
    intro n
    simp [hc]
    replace h2 : b ^ n * b ^ 2 = b ^ n * (4 * b + 1):= by rw [h2]
    replace h1 : a ^ n * a ^ 2 = a ^ n * (4 * a + 1):= by rw [h1]
    ring_nf
    linarith

  -- Establish initial values: c(1) = 4 and c(0) = 2
  replace h2 : c 1 = 4:= by
    simp [hc]
    subst a b
    ring_nf
  replace h1 : c 0 = 2:= by
    simp [hc]
    ring_nf

  -- Prove that all values in sequence c are integers
  have h4 : ∀ n : ℕ, (∃ x : ℤ, c n = x) ∧ (∃ y : ℤ, c (n + 1) = y):= by
    intro n
    induction n with
    | zero =>
      simp [hc]
      subst a b
      refine ⟨?_, ?_⟩
      .
        use 2
        simp
        ring_nf
      .
        use 4
        simp
        ring_nf
    | succ n ih =>
      rcases ih with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [show n + 1 + 1 = n + 2  by omega]
      rw [h3 n]
      use (4 * y + x)
      rw [hx, hy]
      simp
  replace h4 : ∀ n : ℕ, (∃ x : ℤ, c n = x):= by
    intro n
    exact (h4 n).1

  -- Prove that floor of a^k equals c(k)
  have h5 : ⌊a ^ k⌋ = c k:= by
    specialize h4 k
    rcases h4 with ⟨x, hx⟩
    rw [hx]
    simp [hc] at hx
    suffices ⌊a ^ k⌋ = x by rify at this ; linarith
    apply Int.floor_eq_iff.2
    set d:= -b with hd
    clear_value d
    replace hd : b = -d:= by linarith
    rw [hd] at hx
    replace hd : d = √5 - 2:= by linarith
    ring_nf at hx
    rw [show (-1 : ℝ) ^ k = -1 by exact Odd.neg_one_pow hk] at hx
    have hd1 : d ≥ 0:= by
      subst d
      have g : (5 : ℝ) ≥ 2 ^ 2:= by linarith
      replace g : √5 ≥ √(2 ^ 2):= by exact Real.sqrt_le_sqrt g
      field_simp at g
      linarith
    have hd2 : d < 1:= by
      subst d
      have g : (5 : ℝ) ≤ (5 / 2) ^ 2:= by linarith
      replace g:= Real.sqrt_le_sqrt g
      field_simp at g
      linarith
    have hd3 : d ^ k ≥ 0:= by positivity
    have hd4 : d ^ k < 1:= by refine pow_lt_one₀ hd1 hd2 (by exact Nat.ne_of_odd_add hk)
    rw [←hx]
    refine ⟨by linarith, by linarith⟩

  -- Prove that c(n+1) ≥ 4 for all n
  have h6 : ∀ n : ℕ, c (n + 1) ≥ 4 ∧ c (n + 2) ≥ 4:= by
    intro n
    induction n with
    | zero =>
      simp
      rw [h3 0, h2, h1]
      norm_num
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [show n + 2 + 1 = n + 3 by omega]
      specialize h3 (n + 1)
      rw [show n + 1 + 2 = n + 3 by omega] at h3
      rw [h3]
      rw [show n + 1 + 1 = n + 2 by omega]
      refine ⟨by linarith, by linarith⟩
  replace h6 : ∀ n : ℕ, c (n + 1) ≥ 4:= by
    intro n
    exact (h6 n).1

  -- Prove that all values in sequence c are even numbers
  have h7 : ∀ n : ℕ, (∃ x : ℤ, c n = 2 * x) ∧ (∃ y : ℤ, c (n + 1) = 2 * y):= by
    intro n
    induction n with
    | zero =>
      simp
      rw [h1, h2]
      constructor
      .
        use 1
        simp
      .
        use 2
        simp
        ring_nf
    | succ n ih =>
      rcases ih with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [h3 n, hx, hy]
      use (4 * y + x)
      simp
      ring_nf
  replace h7 : ∀ n : ℕ, (∃ x : ℤ, c n = 2 * x):= by
    intro n
    exact (h7 n).1

  -- Final contradiction: show that floor of a^k is even and greater than 2,
  -- therefore cannot be prime
  by_contra H
  specialize h7 k
  rcases h7 with ⟨q, hq⟩
  rw [hq] at h5
  have hk1 : k ≠ 0:= by exact Nat.ne_of_odd_add hk
  specialize h6 (k - 1)
  rw [show k - 1 + 1 = k by omega] at h6
  replace h6 : q ≥ 2:= by
    rify
    linarith
  replace h5 : ⌊a ^ k⌋ = 2 * q:= by
    rify
    linarith
  rw [h5] at H
  replace H : Nat.Prime ((2 * q).natAbs):= by exact Int.prime_iff_natAbs_prime.mp H
  have g : 2 ∣ (2 * q).natAbs:= by
    zify
    rw [abs_of_pos (by linarith)]
    simp
  have g1 : Nat.Prime 2:= by decide
  replace g2 : 2 = (2 * q).natAbs:= by exact (Nat.prime_dvd_prime_iff_eq g1 H).mp g
  zify at g2
  rw [abs_of_pos (by linarith)] at g2
  linarith
