import Mathlib

open Finset Classical

/-- An auxiliary lemma: There exists an arithmetic progression of length $N$ containing
  exactly $n$ integers if and only if there exists a $k$ such that
  $kn - k + 1 \leq N \leq kn + k - 1$. -/
lemma exists_arithmetic_progression_iff {N n : ℕ} (hn : 2 ≤ n) :
    (∃ a₀ d : ℝ, Nat.count (fun i : ℕ => a₀ + d * i ∈ Set.range Int.cast) N = n) ↔
    (∃ k, k * n - k + 1 ≤ N ∧ N ≤ k * n + k - 1) := by
  refine ⟨fun | ⟨a₀, d, count_eq⟩ => ?_, fun | ⟨k, hk⟩ => ?_⟩
  · -- Forward direction: Scale the sequence of indices so that the $n$ integers are
    -- exactly $0, \cdots, n - 1$. We define a predicate $P$ meaning "the $i$-th term of
    -- the sequence is an integer".
    set P := fun i : ℕ => a₀ + d * i ∈ Set.range Int.cast with P_def
    -- We restate the condition `count_eq` using the predicate $P$.
    simp only [← P_def] at count_eq
    clear P_def
    -- Let $u, v$ be the positions of the first and second integers in the sequence.
    -- From these positions, we can calculate the distance between two consecutive integers
    -- in the sequence and use this distance as a scaling factor.
    let u := Nat.nth P 0
    let v := Nat.nth P 1
    -- If the set $P$ were finite (in reality, it must be infinite since integers appear
    -- at intervals of $v - u$), its size would be sufficient.
    have card_P_enough {i : ℕ} (hi : i < 2) (hP : (setOf P).Finite) : i < #hP.toFinset := calc
      _ < 2 := hi
      _ ≤ n := hn
      _ = _ := count_eq.symm
      _ ≤ _ := Nat.count_le_card hP _
    -- Both $u$ and $v$ satisfy property $P$.
    have P_u : P u := Nat.nth_mem _ (card_P_enough (by simp))
    have P_v : P v := Nat.nth_mem _ (card_P_enough (by simp))
    -- $u$ is less than $v$ (by `Nat.nth_lt_nth'`)
    have u_lt_v : u < v := Nat.nth_lt_nth' (by simp) (card_P_enough (by simp))
    -- $v$ is less than $N$: Since there are at least $2$ natural numbers
    -- between $0$ and $N - 1$ that satisfy $P$.
    have v_lt_N : v < N := Nat.nth_lt_of_lt_count (count_eq ▸ hn)
    -- Clear redundant conditions
    clear card_P_enough
    -- $u$ is indeed the first index satisfying $P$: For all $i < u$, $P_i$ does not hold.
    have not_P_of_lt_u : ∀ i < u, ¬P i := by
      rw [← Nat.le_find_iff, ← Nat.nth_zero_of_exists]
      exact ⟨u, P_u⟩
    -- $v$ is indeed the second index satisfying $P$: For all $i$ between $u$ and $v$,
    -- $P_i$ does not hold.
    have not_P_of_between_u_v : ∀ i, u < i → i < v → ¬P i := by
      intro i hi hi'
      refine fun h => absurd (Nat.le_nth_of_lt_nth_succ hi' h) ?_
      linarith
    -- Define the distance between two integers as $k$.
    let k := v - u
    -- A "shift" lemma for $P$: If $P_i$ and $P_j$ both hold, then $P_k$ implies $P_l$
    -- for any $k \equiv l \pmod{j - i}$.
    have P_shift {i j k l : ℕ}
        (P_i : P i) (P_j : P j) (le : i ≤ j)
        (P_k : P k) (mod_eq : k ≡ l [MOD j - i]) : P l := by
      obtain ⟨x_i, hx_i⟩ := P_i
      obtain ⟨x_j, hx_j⟩ := P_j
      obtain ⟨x, hx⟩ := P_k
      rw [Nat.modEq_iff_dvd, Nat.cast_sub le] at mod_eq
      obtain ⟨m, hm⟩ := mod_eq
      refine ⟨x + m * (x_j - x_i), ?_⟩
      rify at hm ⊢
      rw [hx, hx_i, hx_j, add_sub_add_left_eq_sub, ← mul_sub,
        mul_comm (m : ℝ), mul_assoc, ← hm]
      ring
    -- Using the shift lemma, we can prove $u < k$; otherwise, $u - k$ would also satisfy $P$,
    -- contradicting the minimality of $u$.
    have u_lt_k : u < k := by
      by_contra h
      simp at h
      refine not_P_of_lt_u (u - k) ?_ (P_shift P_u P_v (by linarith) P_u ?_)
      · omega
      · rw [Nat.modEq_iff_dvd]
        use -1
        omega
    -- For any $i$, $u + ki$ also satisfies $P$.
    have P_u_add_multiple_of_k (i : ℕ) : P (u + k * i) := by
      refine P_shift P_u P_v (by linarith) P_u ?_
      rw [Nat.modEq_iff_dvd]
      use i
      push_cast
      ring
    -- The predicate $P$ is actually equivalent to "being congruent to $u$ modulo $k$".
    have P_eq : P = (· ≡ u [MOD k]) := by
      ext i
      refine ⟨fun P_i => ?_, fun h => ?_⟩
      · -- Forward: Assume $P_i$ holds but $i$ does not fall in the congruence class of $u$
        -- modulo $k$. Then $P_{u + (i - u) \% k}$ holds, contradicting "no index between
        -- $u$ and $v$ satisfies $P$".
        have u_le_i := not_lt.mp (fun lt => not_P_of_lt_u _ lt P_i)
        have : P (u + k * ((i - u) / k)) := P_u_add_multiple_of_k _
        replace : P (u + (i - u) % k) := P_shift this P_i ?_ P_u ?_
        -- Given $P_{u + (i - u) \% k}$, we prove $i \equiv u \pmod{k}$.
        -- Otherwise, $(i - u) \% k$ is non-zero and less than $k$,
        -- so $u + (i - u) \% k$ lies between $u$ and $v$, leading to a contradiction.
        · rw [Nat.modEq_iff_dvd, dvd_sub_comm, ← Nat.cast_sub u_le_i,
            Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
          by_contra h
          refine not_P_of_between_u_v _ (by omega) ?_ this
          rw [(Nat.sub_eq_iff_eq_add' (le_of_lt u_lt_v)).mp rfl, add_lt_add_iff_left]
          apply Nat.mod_lt
          simpa [k]
        -- These two goals are trivial arithmetic manipulations.
        · calc
            _ ≤ u + (i - u) := by simp [Nat.mul_div_le]
            _ ≤ _ := by omega
        · have i_eq := Nat.eq_add_of_sub_eq u_le_i (Nat.div_add_mod (i - u) k).symm
          rw [add_comm, ← add_assoc] at i_eq
          rw [Nat.sub_eq_of_eq_add' i_eq, Nat.modEq_iff_dvd]
          use 1
          push_cast
          ring
      · -- Reverse: If $i \equiv u \pmod{k}$, then $P_i$ clearly holds by the shift lemma.
        exact P_shift P_u P_v (by linarith) P_u h.symm
    -- Clear some temporary lemmas.
    clear P_u P_v not_P_of_lt_u not_P_of_between_u_v P_shift P_u_add_multiple_of_k
    -- Using `Nat.count_modEq_card_eq_ceil`, we can compute the value of $n$ explicitly.
    have n_eq : ⌈(N - u : ℚ) / k⌉ = n := by
      simp only [← count_eq, P_eq]
      rw [Nat.count_modEq_card_eq_ceil _ (by omega), Nat.mod_eq_of_lt u_lt_k]
    clear count_eq u_lt_v P_eq
    -- Through some algebraic manipulation, we can prove that $k$ satisfies the condition.
    use k
    rw [Int.ceil_eq_iff,
      div_le_iff₀ (by simp; omega), lt_div_iff₀ (by simp; omega),
      lt_sub_iff_add_lt, sub_le_iff_le_add, sub_mul, one_mul, ← mul_comm (k : ℚ)] at n_eq
    push_cast at n_eq
    -- After clearing denominators in `n_eq`, we get $kn - k + u < N, N \leq kn + u$.
    -- Combined with $0 \leq u < k$, we obtain the conclusion.
    rw [Nat.add_one_le_iff]
    qify
    refine ⟨lt_of_le_of_lt ?_ n_eq.1, le_trans n_eq.2 ?_⟩
    · rw [Nat.cast_sub (Nat.le_mul_of_pos_right _ (by omega))]
      simp
    · norm_cast
      omega
  · /- Given $k$, we explicitly construct an arithmetic progression.

      Here, setting `α := N - k * n` is a clever trick:

      If $N \leq kn$, then by Lean's definition of natural number subtraction,
      $\alpha = 0$, so the sequence is $0, \frac{1}{k}, \frac{2}{k}, \cdots, \frac{N - 1}{k}$.
      But this method can only construct sequences with no more than $kn$ terms, otherwise
      $\frac{kn}{k}$ would be the $n + 1$-th integer, contradicting the requirement that
      the sequence has exactly $n$ integers.

      So if $N > kn$, we need to add $N - kn$ elements to the left of the sequence,
      making it $\frac{-\alpha}{k}, \frac{1 -\alpha}{k}, \cdots, \frac{N - 1 - \alpha}{k}$. -/
    let α := N - k * n
    use -α / k, 1 / k
    simp only [one_div_mul_eq_div, ← add_div]
    -- `k` is non-zero; this lemma will be used frequently since $k$ is in the denominator.
    have k_nz : k ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      intro k_eq
      simp [k_eq] at hk
      omega
    convert_to Nat.count (fun i => i ≡ α [MOD k]) N = n
    · -- We note that the $i$-th term is an integer if and only if $i \equiv \alpha \pmod{k}$.
      congr! 2 with i
      refine ⟨fun | ⟨x, hx⟩ => ?_, fun hi => ?_⟩
      · rw [eq_div_iff_mul_eq (by simpa)] at hx
        rw [Nat.modEq_iff_dvd]
        use -x
        norm_cast at hx
        rw [← sub_eq_zero, mul_comm (k : ℤ), neg_mul, sub_neg_eq_add, hx]
        ring
      · -- Use `Nat.modEq_iff_dvd` to convert congruence to divisibility.
        rw [Nat.modEq_iff_dvd] at hi
        obtain ⟨m, hm⟩ := hi
        use -m
        rw [eq_div_iff_mul_eq (by simpa), mul_comm, Int.cast_neg, mul_neg]
        norm_cast
        rw [← hm]
        ring
    · -- Compute using `Nat.count_modEq_card_eq_ceil`.
      zify
      rw [Nat.count_modEq_card_eq_ceil _ (by omega), Nat.mod_eq_of_lt (by omega),
        Int.ceil_eq_iff, lt_div_iff₀ (by simp; omega), div_le_iff₀ (by simp; omega),
        lt_sub_iff_add_lt, sub_le_comm, sub_mul, one_mul, ← mul_comm (k : ℚ)]
      norm_cast
      simp only [Int.subNatNat_eq_coe]
      refine ⟨by omega, Int.le_natCast_sub _ _⟩

/-- An alternative formulation of the theorem `exists_arithmetic_progression_iff`:

  "There exists a $k$ such that $kn - k + 1 \leq N \leq kn + k - 1$" can be replaced with
  $N \neq 0$ and $N / (n + 1) < (N - 1) / (n - 1)$.

  This is because $kn - k + 1 \leq N$ is equivalent to $k \leq \frac{N - 1}{n - 1}$, which in
  turn is equivalent to $k \leq \lfloor \frac{N - 1}{n - 1} \rfloor$
  (Lean's natural number division automatically rounds down, so we can just write `/`).
  Similarly, $N \leq kn + k - 1$ is equivalent to $kn + k > N$, which means
  $k > \frac{N}{n + 1}$, i.e., $k > \lfloor \frac{N}{n + 1} \rfloor$.

  An interval $(a, b] \cap \mathbb N$ is non-empty if and only if $a < b$. Thus,
  the original condition is equivalent to $\lfloor \frac{N}{n + 1} \rfloor <
  \lfloor \frac{N - 1}{n - 1} \rfloor$. -/
lemma exists_arithmetic_progression_iff' {N n : ℕ} (hn : 2 ≤ n) :
    (∃ a₀ d : ℝ, Nat.count (fun i : ℕ => a₀ + d * i ∈ Set.range Int.cast) N = n) ↔
    N ≠ 0 ∧ N / (n + 1) < (N - 1) / (n - 1) := by
  by_cases hN : N = 0
  · simp [hN]
    omega
  · rw [ne_eq, eq_true hN, true_and, exists_arithmetic_progression_iff hn,
      ← Nat.sub_pos_iff_lt, ← Nat.card_Ioc, Finset.card_pos, Finset.Nonempty]
    conv_rhs => enter [1, x]; rw [mem_Ioc, and_comm]
    congr! 3 with k
    · rw [Nat.le_div_iff_mul_le (by omega), Nat.le_sub_iff_add_le, Nat.mul_sub, mul_one]
      omega
    · by_cases hk : k = 0
      · simpa [hk]
      · conv_rhs => rw [Nat.div_lt_iff_lt_mul (by omega)]
        rw [Nat.le_sub_iff_add_le (by omega), Nat.add_one_le_iff, Nat.mul_add, mul_one]

/-- Find the smallest positive integer $n$ with the following property:
  There does not exist an arithmetic progression of 1999 terms of real numbers
  containing exactly $n$ integers. -/
theorem algebra_604646 :
    IsLeast {n : ℕ | 0 < n ∧ ¬∃ a₀ d : ℝ,
    Nat.count (fun i : ℕ => a₀ + d * i ∈ Set.range Int.cast) 1999 = n} 70 := by
  simp only [IsLeast, lowerBounds, Set.mem_setOf_eq]
  refine ⟨⟨by simp, fun h => ?_⟩, fun | n, ⟨n_pos, hn⟩ => ?_⟩
  · -- $n = 70$ satisfies the condition.
    rw [exists_arithmetic_progression_iff' (by simp)] at h
    simp at h
  · by_cases n_ge_2 : 2 ≤ n
    · -- Any number less than 70 does not satisfy the condition, as can be simplified
      -- using `exists_arithmetic_progression_iff'`.
      rw [exists_arithmetic_progression_iff' n_ge_2] at hn
      contrapose! hn
      refine ⟨by simp, ?_⟩
      clear n_pos
      revert n
      refine (?_ : ?p)
      simpa using show (?p : Bool) by rfl
    · -- The case $n = 1$: Consider the sequence $0, \pi, 2\pi, \cdots, 1998\pi$.
      -- Since $\pi$ is irrational, it contains only one integer.
      obtain ⟨_⟩ : n = 1 := by omega
      refine (hn ⟨0, Real.pi, ?_⟩).elim
      set N := 1999 with N_def
      clear_value N
      convert_to Nat.count (· = 0) N = 1
      · congr! 2 with i
        simp
        refine ⟨fun | ⟨x, hx⟩ => ?_, fun i_eq => by simp [i_eq]⟩
        by_contra h
        -- The theorem `irrational_pi` in `Mathlib` states that $\pi$ is irrational.
        refine irrational_pi ⟨x / i, ?_⟩
        field_simp
        exact hx
      · simp [Nat.count_eq_card_filter_range, N_def]
