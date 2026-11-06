import Mathlib

open Real Polynomial

/-- The zeroes of the function $f(x)=x^2-ax+2a$ are integers. What is the sum of the possible
values of $a?$

$\textbf{(A)}\ 7\qquad\textbf{(B)}\ 8\qquad\textbf{(C)}\ 16\qquad\textbf{(D)}\
17\qquad\textbf{(E)}\ 18$ -/
theorem algebra_95239 (s : Set ℂ) (f : ℂ → ℂ[X]) (hf : ∀ a : ℂ, f a = X^2 + C (-a) * X + C (2 * a))
    (hs : s = {a : ℂ | ∃ n m : ℤ, (f a).roots = {(n:ℂ), (m:ℂ)}}) :
    ∃ _ : Fintype s, ∑ a ∈ s, a = 16 := by

  -- For any $a \in \bb{C}$, let $f_a(X) = X^2 - a X + 2 a$.
  -- Let $s$ be the set of $a \in \bb{C}$ such that the roots of $f_a$ are integers.

  -- We will actually show that $s = \{-1, 0, 8, 9\}.
  suffices s = {-1, 0, 8, 9} from ?_
  · subst this
    refine ⟨?_, ?_⟩
    · exact Set.fintypeInsert' (-1) {0, 8, 9}
    · simp
      rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
          Finset.sum_insert (by norm_num), Finset.sum_singleton]
      norm_num

  ext a
  constructor; swap

  -- First, let's show that $-1, 0, 8, 9$ are in $s$. Let's calculate the roots of
  --$f_{-1}, f_0, f_8, f_9$
  · rintro (rfl | rfl | rfl | rfl) <;> simp only [hs, Set.mem_setOf_eq]

    -- Let's start with $f_{-1}$. We will show that the roots of $f_{-1}$ are $1$ and $-2$.
    · suffices (f (-1)).roots = {1, -2} from ?_
      · simp [this]
        use 1, -2
        simp

      -- We can factor $f_{-1}$ as $(x - 1)(x + 2)$.
      have : f (-1) = (X - C 1) * (X - C (-2)) := by
        symm
        calc _ = (X:ℂ[X])^2 + -(C (-2) + C 1) * X + C (-2) * C 1 := by ring
            _ = X^2 + C 1 * X + C (-2) * C 1 := by congr; nth_rw 1 [←map_add, ←map_neg]; congr; ring
            _ = X^2 + X + C (-2) := by rw [←map_mul, map_one, one_mul, mul_one]
            _ = _ := by rw [hf, neg_neg, mul_neg_one, map_one, one_mul]

      -- Therefore, the roots of $f_{-1}$ are $1$ and $-2$.
      rw [this, roots_mul, roots_X_sub_C, roots_X_sub_C]; rfl
      apply ne_zero_of_ne_zero_of_monic (p := X) (by exact X_ne_zero)
      monicity!

    -- Now, let's look at $f_0$. We have $$f_0 = X^2$, so the only root of $f_0$ is $0$.
    · simp [hf]
      use 0, 0
      simp
      rfl

    -- Now, let's look at $f_8$. We will show that the only root of $f_8$ is $4$.
    · suffices (f 8).roots = {4, 4} from ?_
      · simp [this]
        use 4, 4
        simp

      -- We can factor $f_8$ as $(x - 4)^2$.
      have : f 8 = (X - C 4)^2 := by
        symm
        calc _ = (X:ℂ[X])^2 + -(C 4 + C 4) * X + C 4 * C 4 := by ring
            _ = X^2 + C (-8) * X + C 16 := by rw [←map_add, ←map_neg, ←map_mul]; norm_num
            _ = _ := by rw [hf]; norm_num

      -- Therefore, the only root of $f_8$ is $4$.
      rw [this, roots_pow, roots_X_sub_C]; rfl

    -- Finally, let's look at $f_9$. We will show that the roots of $f_9$ are $3$ and $6$.
    · suffices (f 9).roots = {3, 6} from ?_
      · simp [this]
        use 3, 6
        simp

      -- We can factor $f_9$ as $(x - 3)(x - 6)$.
      have : f 9 = (X - C 3) * (X - C 6) := by
        symm
        calc _ = (X:ℂ[X])^2 + -(C 6 + C 3) * X + C 6 * C 3 := by ring
            _ = X^2 + C (-9) * X + C 18 := by rw [←map_add, ←map_neg, ←map_mul]; norm_num
            _ = _ := by rw [hf]; norm_num

      -- Therefore, the roots of $f_9$ are $3$ and $6$.
      rw [this, roots_mul, roots_X_sub_C, roots_X_sub_C]; rfl
      apply ne_zero_of_ne_zero_of_monic (p := X) (by exact X_ne_zero)
      monicity!



  -- Now, let $a \in s$. We will show that $x \in \{-1, 0, 8, 9\}$.
  · intro ha
    rw [hs, Set.mem_setOf] at ha
    -- Let $m, n$ be the roots of $f_a$.
    rcases ha with ⟨m, n, hfmn⟩

    -- Because $f_a$ is a degree 2 polynomial with 2 roots, we can write $f_a(x) = (x - m)(x - n)$.
    have : f a = (X - C (m:ℂ)) * (X - C (n:ℂ)) := by
      rw [←Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (p := f a)]
      · rw [hfmn]
        simp
      · rw [hf]
        monicity!
      · simp [hfmn]
        rw [hf]
        symm
        compute_degree!

    -- Expanding the parentheses, we get $f_a(x) = x^2 - (m + n) x + m n$.
    have hf' : f a = X^2 + C (-(m:ℂ) + -n) * X + C ((m:ℂ) * n) := by
      rw [map_add, map_neg, map_neg, map_mul, this]
      ring

    -- We also know $f_a (x) = x^2 - a x + 2 a$.

    -- On the one hand, the $X$ coefficient of $f_a$ is $-a$.
    have : (f a).coeff 1 = - a := by
      rw [hf]
      simp

    -- On the other hand, the $X$ coefficient of $f_a$ is $-(m + n)$.
    have : (f a).coeff 1 = -(m + n) := by
      rw [hf', coeff_add, coeff_add, coeff_C_mul_X, coeff_X_pow, coeff_C]
      simp
      ring

    -- Therefore, $a = m + n$.
    have hamn : a = m + n := by
      calc _ = -(-a) := by ring
           _ = -(f a).coeff 1 := by congr; symm; assumption
           _ = -(-(m + n)) := by congr
            _ = _ := by ring

    -- On the one hand, the constant coefficient of $f_a$ is $2 a$.
    have : (f a).coeff 0 = 2 * a := by
      rw [hf]
      simp

    -- On the other hand, the constant coefficient of $f_a$ is $m n$.
    have : (f a).coeff 0 = m * n := by
      rw [hf', coeff_add, coeff_add, coeff_C_mul_X, coeff_X_pow, coeff_C]
      simp

    -- Therefore, $2 a = m n$.
    have hamn2 : 2 * a = m * n := by
      calc _ = 2 * a := by ring
           _ = (f a).coeff 0 := by symm; assumption
           _ = m * n := by congr

    -- The equation $a = m + n$ tells us that $a$ is an integer.
    have : ∃ a₀ : ℤ, a = a₀ := by
      use m + n
      simp [hamn]
    rcases this with ⟨a₀, rfl⟩

    norm_cast at hamn
    norm_cast at hamn2
    suffices a₀ ∈ ({-1, 0, 8, 9} : Set ℤ) by simp; norm_cast
    clear! s f

    -- Eliminating $a$ from the equations, we get $m n = 2 m + 2 n$
    have hmn : m * n = 2 * m + 2 * n := by omega

    -- Right hand side is even, so either $m$ or $n$ is even.
    have : Even m ∨ Even n := by
      rw [←Int.even_mul, hmn, ←mul_add]
      simp

    -- Without loss of generality, assume that $n$ is even.
    wlog hne : Even n generalizing n m
    · apply this n m
      · rw [hamn, add_comm]
      · rw [hamn2, mul_comm]
      · rw [mul_comm, hmn, add_comm]
      · rwa [or_comm]
      · tauto

    -- Write $n = 2 n_0$.
    have : ∃ n₀, n = 2 * n₀ := by exact Even.exists_two_nsmul n hne
    rcases this with ⟨n₀, rfl⟩

    -- Substituting $n = 2 n_0$ into $m n = 2 m + 2 n$, we get $m n_0 = m + 2 n_0$.
    replace hmn : m * n₀ = m + 2 * n₀ := by linarith

    -- Every term in this expression, except $m$, is divisible by $n_0$, so $m$ is divisible by $n_0$.
    have : n₀ ∣ m := by
      use m - 2
      nlinarith

    -- Write $m = n_0 m_0$.
    have : ∃ m₀, m = n₀ * m₀ := by exact this
    rcases this with ⟨m₀, rfl⟩

    -- If $n_0 = 0$, then $m_0 = 0$, and hence $a = 0$ which is in $\{-1, 0, 8, 9\}$.
    by_cases hn₀ : n₀ = 0
    · subst hn₀
      simp [hamn]
    -- Therefore, assume that $n_0 \neq 0$.

    -- Substituting $m = n_0 m_0$ into $m n_0 = m + 2 n_0$, we get $n_0 m_0 = m_0 + 2$.
    replace hmn : n₀ * m₀ = m₀ + 2 := by
      calc _ = (n₀ * (n₀ * m₀)) / n₀ := by exact Int.eq_ediv_of_mul_eq_right hn₀ rfl
           _ = (n₀ * m₀ * n₀) / n₀ := by ring_nf
           _ = (n₀ * m₀ + 2 * n₀) / n₀ := by rw [hmn]
           _ = (n₀ * (m₀ + 2)) / n₀ := by ring_nf
           _ = _ := by exact Int.mul_ediv_cancel_left (m₀ + 2) hn₀

    -- Every term in this expression, except 2, is divisible by $m_0$, so $2$ is divisible by $m_0$.
    have : m₀ ∣ 2 := by
      use n₀ - 1
      linarith
    have : (m₀).natAbs ∣ 2 := by exact Int.ofNat_dvd_right.mp this
    have : (m₀).natAbs ∈ (2).divisors := by simpa
    have : (m₀).natAbs ∈ ({1, 2} : Finset ℕ) := by exact this
    have : m₀.natAbs = 1 ∨ m₀.natAbs = 2 := by simpa
    have : m₀ = 1 ∨ m₀ = -1 ∨ m₀ = 2 ∨ m₀ = -2 := by omega

    -- Let's look at each case.
    rcases this with (rfl | rfl | rfl | rfl)

    -- If $m_0 = 1$, then $n_0 = 3$. And hence $a = 9$ which is in $\{-1, 0, 8, 9\}$.
    · have : n₀ = 3 := by omega
      subst this
      have : a₀ = 9 := by exact hamn
      subst this
      simp

    -- If $m_0 = -1$, then $n_0 = -1$. And hence $a = -1$ which is in $\{-1, 0, 8, 9\}$.
    · have : n₀ = -1 := by omega
      subst this
      have : a₀ = -1 := by exact hamn
      subst this
      simp

    -- If $m_0 = 2$, then $n_0 = 2$. And hence $a = 8$ which is in $\{-1, 0, 8, 9\}$.
    · have : n₀ = 2 := by omega
      subst this
      have : a₀ = 8 := by exact hamn
      subst this
      simp

    -- If $m_0 = -2$, then $n_0 = -2$. And hence $a = 0$ which is in $\{-1, 0, 8, 9\}$.
    · have : n₀ = -2 := by omega
      subst this
      have : a₀ = 0 := by exact hamn
      subst this
      simp