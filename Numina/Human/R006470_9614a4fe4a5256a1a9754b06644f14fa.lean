import Mathlib
/- Let $N$ be an integer greater than 1 and $D$ be a positive even integer. Determine the sum of all positive even integers $x$ such that $x < N$ and $x$ is not divisible by $D$. Show that this sum is equal to $M(M+1) - (D/2)P(P+1)$, where $M = \lfloor (N-1)/2 \rfloor$ and $P = \lfloor M/(D/2) \rfloor$. -/
theorem number_theory_637428 (n d m p : ℕ) (f : ℕ → ℕ) (hn : n > 1) (hd : d > 0) (h1 : Even d) (hf : ∀ x : ℕ, f x = if (d ∣ x ∨ Odd x) then 0 else x) (hm : m = (n - 1) / 2) (hp : p = m / (d / 2)) : ∑ i in Finset.range n, f i = m * (m + 1) - d / 2 * p * (p + 1):= by
  -- Extract the even number d as 2 * d
  rcases h1 with ⟨d, rfl⟩
  simp at hd
  -- Rewrite d + d as 2 * d for clarity
  rw [show d + d = 2 * d by omega] at hf hp ⊢
  simp at hp ⊢
  -- Define helper function g that returns 0 if 2*d divides x, otherwise x
  set g:= fun x : ℕ => if 2 * d ∣ x then 0 else x with hg
  clear_value g
  -- Key lemma: sum of f over range(2*n+1) equals sum of g over even numbers
  have h : ∀ n : ℕ, ∑ i in Finset.range (2 * n + 1), f i = ∑ i in Finset.range (n + 1), g (2 * i):= by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp [hg]
      specialize hf 0
      simp at hf
      exact hf
    | succ n ih =>
      -- Inductive step: n → n+1
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
      -- Define helper variables for clarity
      set a:= 2 * n + 1 with ha
      set b:= n + 1 with hb
      clear_value a b
      -- Expand the sums using range_succ
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      -- Show that f(a) + f(a+1) = g(2*b)
      suffices f a + f (a + 1) = g (2 * b) by omega
      subst a b
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
      -- f(2*n+1) = 0 since 2*n+1 is odd
      have g1 : f (2 * n + 1) = 0:= by
        specialize hf (2 * n + 1)
        simp at hf
        exact hf
      rw [g1]
      simp
      -- Evaluate f(2*(n+1)) using the definition
      specialize hf (2 * (n + 1))
      simp [hg]
      rw [hf]
      -- 2*(n+1) is not odd
      have g2 : ¬Odd (2 * (n + 1)):= by
        by_contra H
        absurd H
        simp
      simp [g2]
  -- Define N = n-1 for convenience
  set N:= n - 1 with hN
  clear_value N
  replace hN : n = N + 1:= by omega
  rw [hN]
  -- Express N in terms of division and remainder
  have g0 : N = 2 * (N / 2) + N % 2:= by omega
  rw [←hm] at g0
  -- Handle the sum based on whether N is even or odd
  have h0 : ∑ i ∈ Finset.range (N + 1), f i = ∑ i ∈ Finset.range (2 * m + 1), f i:= by
    rw [g0]
    mod_cases N % 2
    .
      -- Case: N is even
      rw [H]
    .
      -- Case: N is odd
      rw [H]
      simp
      set t:= 2 * m + 1 with ht
      clear_value t
      rw [Finset.sum_range_succ]
      -- f(t) = 0 since t is odd
      suffices f t = 0 by linarith
      subst t
      specialize hf (2 * m + 1)
      simp at hf
      exact hf
  rw [h0]
  rw [h m]
  -- Key property: g(2*x) + (if 2*d divides 2*x then 2*x else 0) = 2*x
  replace hg : ∀ x : ℕ, (if 2 * d ∣ 2 * x then 2 * x else 0) + g (2 * x) = 2 * x:= by
    intro x
    by_cases hx : x = 0
    .
      -- Case: x = 0
      subst x
      simp [hg]
    .
      -- Case: x ≠ 0
      by_cases hx1 : 2 * d ∣ 2 * x
      all_goals
        simp [hg, hx1]
  -- Sum of g(2*x) and conditional terms equals n*(n+1)
  have h1 : ∀ n : ℕ, (∑ x in Finset.range (n + 1), g (2 * x) + ∑ x in Finset.range (n + 1), (if 2 * d ∣ 2 * x then 2 * x else 0)) = n * (n + 1):= by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp
      specialize hg 0
      simp at hg
      exact hg
    | succ n ih =>
      -- Inductive step: n → n+1
      set m:= n + 1 with hm
      clear_value m
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      specialize hg (n + 1)
      subst m
      linarith
  -- Main goal: show the desired sum formula
  suffices (∑ i ∈ Finset.range (m + 1), g (2 * i)) + d * p * (p + 1) = m * (m + 1) by omega
  subst n
  simp at hn
  specialize h1 m
  -- Rearrange to show the final formula
  suffices m * (m + 1) + d * p * (p + 1) = (∑ x ∈ Finset.range (m + 1), if 2 * d ∣ 2 * x then 2 * x else 0) + m * (m + 1) by omega
  clear hf
  -- Express m in terms of division and remainder by d
  have h1 : m = d * (m / d) + m % d:= by exact Eq.symm (Nat.div_add_mod m d)
  rw [←hp] at h1
  set r:= m % d with hr
  clear_value r
  -- r < d by properties of remainder
  replace hr : r < d:= by
    subst r
    refine Nat.mod_lt m (by omega)
  -- Key lemma: sum of conditional terms for d*k + r + 1 elements
  have h3 : ∀ r : ℕ, r < d → ∀ k : ℕ, (∑ x ∈ Finset.range (d * k + r + 1), if 2 * d ∣ 2 * x then 2 * x else 0) = d * k * (k + 1):= by
    intro r
    induction r with
    | zero =>
      -- Case: r = 0
      intro _
      simp
      intro k
      induction k with
      | zero =>
        -- Base case: k = 0
        simp
      | succ k ih =>
        -- Inductive step: k → k+1
        rw [Finset.sum_range_succ]
        rw [show d * (k + 1) = d * k + 1 + (d - 1) by ring_nf ; omega]
        -- Helper lemma for the sum over d*k + 1 + t elements
        have h3 : ∀ t : ℕ, t < d → (∑ x ∈ Finset.range (d * k + 1 + t), if 2 * d ∣ 2 * x then 2 * x else 0) = (∑ x ∈ Finset.range (d * k + 1), if 2 * d ∣ 2 * x then 2 * x else 0):= by
          intro t ht
          induction t with
          | zero =>
            -- Base case: t = 0
            simp
          | succ t ih1 =>
            -- Inductive step: t → t+1
            replace ih1:= ih1 (by omega)
            rw [show d * k + 1 + (t + 1) = d * k + 1 + t + 1 by omega]
            rw [Finset.sum_range_succ]
            -- Show that 2*d does not divide 2*(d*k + 1 + t)
            have g : ¬(2 * d ∣ 2 * (d * k + 1 + t)):= by
              by_contra H
              have g : 2 ≠ 0:= by omega
              replace H : d ∣ d * k + 1 + t:= by exact (mul_dvd_mul_iff_left g).mp H
              rw [show d * k + 1 + t = d * k + (1 + t) by ring] at H
              have g1 : d ∣ d * k:= by simp
              replace H : d ∣ 1 + t:= by exact (Nat.dvd_add_iff_right g1).mpr H
              have g2 : 1 + t > 0:= by omega
              replace H : d ≤ 1 + t:= by exact Nat.le_of_dvd g2 H
              linarith
            simp [g]
            exact ih1
        rw [h3 (d - 1) (by omega)]
        rw [ih]
        rw [show d * k + 1 + (d - 1) = d * k + d by omega]
        rw [show 2 * (d * k + d) = 2 * d * (k + 1) by ring_nf]
        simp
        ring_nf
    | succ r ih =>
      -- Case: r → r+1
      intro hr1
      replace ih:= ih (by omega)
      intro k
      specialize ih k
      rw [Finset.sum_range_succ]
      -- Show that 2*d does not divide 2*(d*k + (r+1))
      have g : ¬(2 * d ∣ 2 * (d * k + (r + 1))):= by
        by_contra H
        have g : 2 ≠ 0:= by omega
        replace H : d ∣ d * k + (r + 1):= by exact (mul_dvd_mul_iff_left g).mp H
        have g1 : d ∣ d * k:= by simp
        replace H : d ∣ r + 1:= by exact (Nat.dvd_add_iff_right g1).mpr H
        have g2 : r + 1 > 0:= by omega
        replace H : d ≤ r + 1:= by exact Nat.le_of_dvd g2 H
        linarith
      simp [g]
      exact ih
  -- Apply the key lemma with our specific values
  specialize h3 r hr p
  rw [←h1] at h3
  rw [h3]
  -- Final algebraic manipulation
  ring
