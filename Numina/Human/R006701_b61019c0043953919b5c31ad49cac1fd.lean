import Mathlib
/- Let $m$ be a positive integer which is not a perfect square, and let $k_640300 = \lfloor \sqrt{m} \rfloor$.
Let $n$ be a non-negative integer.
Let $X = (\sqrt{m} + k_0)^{2n+1}$.
Let $P$ be the integer part of $X$ and $Q$ be the fractional part of $X$ (i.e. $X = P+Q$, $P \in \mathbb{Z}$, $0 \le Q < 1$).
Show that $Q(P+Q) = (m-k_0^2)^{2n+1}$. -/
theorem number_theory_640300 (m n : ℕ) (P : ℤ) (Q : ℝ) (hm : ¬(IsSquare m)) (hP : P = ⌊(√m + ⌊√m⌋) ^ (2 * n + 1)⌋) (hQ : Q = (√m + ⌊√m⌋) ^ (2 * n + 1) - P) : Q * (P + Q) = (m - ⌊√m⌋ ^ 2) ^ (2 * n + 1):= by
  -- Define key variables: a = √m + ⌊√m⌋ and b = √m - ⌊√m⌋
  set a:= √m + ⌊√m⌋ with ha
  set b:= √m - ⌊√m⌋ with hb
  clear_value a b

  -- Key identity: a * b = m - ⌊√m⌋^2
  have h1 : a * b = m - ⌊√m⌋ ^ 2:= by
    subst a b
    ring_nf
    field_simp
    ring

  -- Rewrite the goal using the key identity
  rw [←h1]
  rw [show P + Q = a ^ (2 * n + 1) by linarith]
  rw [show (a * b) ^ (2 * n + 1) = a ^ (2 * n + 1) * b ^ (2 * n + 1) by exact mul_pow a b (2 * n + 1)]

  -- Main goal reduces to showing Q = b^(2n+1)
  suffices Q = b ^ (2 * n + 1) by rw [this] ; ring
  subst Q

  -- Need to show P = a^(2n+1) - b^(2n+1)
  suffices P = a ^ (2 * n + 1) + -b ^ (2 * n + 1) by linarith
  rw [show -b ^ (2 * n + 1) = (-1 * b) ^ (2 * n + 1) by rw [mul_pow (-1) b (2 * n + 1)] ; field_simp]

  -- Define c = -b for convenience
  set c:= -1 * b with hc
  clear_value c

  -- Key properties of c
  replace h1 : a * c = ⌊√m⌋ ^ 2 - m:= by subst c ; linarith
  replace hc : c = ⌊√m⌋ - √m:= by linarith
  clear hb b

  -- Sum of a and c
  have h2 : a + c = 2 * ⌊√m⌋:= by linarith
  set k:= ⌊√m⌋ with hk
  clear_value k

  -- Prove c < 0 (since m is not a perfect square)
  have hc1 : c < 0:= by
    subst c
    by_contra H
    simp at H
    have g1 : k ≤ √m:= by subst k ; exact Int.floor_le √↑m
    rw [show (↑k : ℝ) = |(↑k : ℝ)| by exact Eq.symm (abs_of_nonneg (by subst k ; positivity))] at H g1
    rw [show √↑m = |√m| by exact Eq.symm (abs_of_nonneg (by positivity))] at H g1
    replace H : √m ^ 2 ≤ k ^ 2:= by exact sq_le_sq.mpr H
    replace g1 : k ^ 2 ≤ √m ^ 2:= by exact sq_le_sq.mpr g1
    field_simp at H g1
    replace g1 : m = k ^ 2:= by rify ; linarith
    absurd hm
    use k.natAbs
    zify
    simp
    linarith

  -- Prove c > -1 (using floor properties)
  have hc2 : c > -1:= by
    subst c
    suffices k + 1 > √m by linarith
    subst k
    exact Int.lt_floor_add_one √↑m

  -- Prove a > 0
  have ha1 : a > 0:= by
    replace hm : m > 0:= by
      by_contra H
      simp at H
      subst m
      simp at hm
    subst a k
    positivity

  -- Key recurrence relation: x^2 = 2kx + (m-k^2) for x = a or x = c
  have h3 : ∀ x : ℝ, x = a ∨ x = c → x ^ 2 = 2 * k * x + (m - k ^ 2):= by
    intro x hx
    rcases hx with hx | hx
    all_goals
      subst x
    .
      subst a
      ring_nf
      field_simp
      ring_nf
    .
      subst c
      ring_nf
      field_simp

  -- Apply the recurrence relation to a and c
  have ga:= h3 a (by simp)
  have gc:= h3 c (by simp)

  -- Prove that a^n + c^n and a^(n+1) + c^(n+1) are integers for all n
  have h4 : ∀ n : ℕ, (∃ k1 : ℤ, a ^ n + c ^ n = k1) ∧ (∃ k2 : ℤ, a ^ (n + 1) + c ^ (n + 1) = k2):= by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      use 2
      simp
      linarith
      use 2 * k
      simp
      linarith
    | succ n ih =>
      rcases ih with ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
      refine ⟨⟨k2, hk2⟩, ?_⟩
      rw [show a ^ (n + 1 + 1) = a ^ 2 * a ^ n by ring_nf]
      rw [show c ^ (n + 1 + 1) = c ^ 2 * c ^ n by ring_nf]
      rw [show a ^ (n + 1) = a * a ^ n by ring_nf] at hk2
      rw [show c ^ (n + 1) = c * c ^ n by ring_nf] at hk2
      replace ga : a ^ 2 * a ^ n = (2 * ↑k * a + (↑m - ↑k ^ 2)) * a ^ n:= by rw [ga]
      replace gc : c ^ 2 * c ^ n = (2 * ↑k * c + (↑m - ↑k ^ 2)) * c ^ n:= by rw [gc]
      use 2 * k * k2 + (m - k ^ 2) * k1
      simp
      rw [ga, gc, ←hk1, ←hk2]
      linarith

  -- Apply the result for n = 2n
  replace h4:= (h4 (2 * n)).2
  rcases h4 with ⟨k2, hk2⟩
  rw [hk2]

  -- Need to show P = k2 (the integer part)
  suffices P = k2 by rify at this ; exact this
  subst P

  -- Use floor definition to prove P = ⌊a^(2n+1)⌋
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  .
    rw [←hk2]
    suffices c ^ (2 * n + 1) < 0 by linarith
    refine Odd.pow_neg (by simp) hc1
  .
    rw [←hk2]
    suffices c ^ (2 * n + 1) > -1 by linarith
    rw [show c = (-1) * (-c) by simp]
    rw [mul_pow _ _ (2 * n + 1)]
    rw [show (-1 : ℝ) ^ (2 * n + 1) = -1 by refine Odd.neg_one_pow (by simp)]
    suffices (-c) ^ (2 * n + 1) < 1 by linarith
    replace hc1 : -c ≥ 0:= by linarith
    replace hc2 : -c < 1:= by linarith
    refine pow_lt_one₀ hc1 hc2 (by omega)
