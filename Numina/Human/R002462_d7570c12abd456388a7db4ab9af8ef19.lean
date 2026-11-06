import Mathlib

open Finset

/-- A triangular array of numbers has a first row consisting of the odd integers $1,3,5,\ldots,99$
in increasing order. Each row below the first has one fewer entry than the row above it, and the
bottom row has a single entry. Each entry in any row after the top row equals the sum of the two
entries diagonally above it in the row immediately above it. How many entries in the array are
multiples of $67$? -/
theorem number_theory_93817 (a : ℕ → ℕ → ℕ) (ha1 : ∀ j, a 0 j = 2 * j + 1)
    (ha2 : ∀ i, ∀ j, a (i + 1) j = a i j + a i (j + 1))
    (t : Finset (ℕ × ℕ)) (ht : t = {p ∈ range 50 ×ˢ range 50 | p.1 + p.2 < 50})
    (s : Finset (ℕ × ℕ)) (hs : s = {p ∈ t | 67 ∣ a p.1 p.2}) : s.card = 17 := by


  -- Let the $k$th number in the $n$th row be $a(n,k)$. Writing out some numbers, we find that
  -- $a(i,j) = 2^{i}(i + 2j + 1)$.
  -- We can prove this by induction on $i$.
  have a_eq {i j} : a i j = 2^i * (i + 2 * j + 1) := by
    induction' i with i ih generalizing j
    -- For the base case, we want to show that $a(0,j) = 2^0 (0 + 2j + 1) = 2j + 1$. This is true
    -- by assumption.
    · rw [ha1]
      ring
    -- For the induction step, we can apply the relation $a(i+1,j) = a(i,j) + a(i,j+1)$. Then, using
    -- the induction hypothesis and simplifying, we get the desired result.
    · rw [ha2, ih, ih, ←mul_add, pow_succ, mul_assoc]
      congr 1
      ring


  -- We wish to find all $(n,k)$ such that $67| a(n,k) = 2^{n-1} (n+2k-2)$.

  -- Since $2^{n}$ and $67$ are relatively prime, $67 | 2^{n-1} (n+2k-2)$ if and only if $67 |
  -- n+2k-2$.
  have sixty_seven_dvd_a_iff (i j) : 67 ∣ a i j ↔ 67 ∣ i + 2 * j + 1 := by
    rw [a_eq, Nat.Coprime.dvd_mul_left]
    apply Nat.Coprime.pow_right
    norm_num

  -- Since every row has one less element than the previous row, $0 \le k \lt 50-n$ (the first row
  -- has $50$ elements, the second $49$, and so forth; so $k$ can range from $0$ to $49$ in the
  -- first row, and so forth). Hence $n+2k \lt n + 2(50-n) - 2 = 100 - n \lt 100,$
  have {i j} (hi : i < 50) (hij : i + j < 50) : i + 2 * j < 100 := by linarith only [hi, hij]

  -- it follows that $67 | n - 2k + 2$ implies that $n-2k+2 = 67$ itself.
  replace sixty_seven_dvd_a_iff {i j} (hi : i < 50) (hij : i + j < 50) : 67 ∣ a i j ↔
      66 = i + 2 * j := by
    rw [sixty_seven_dvd_a_iff]
    constructor
    · intro h
      symm
      suffices i + 2 * j + 1 = 67 by linarith only [this]
      apply Nat.eq_of_dvd_of_lt_two_mul
      · positivity
      · exact h
      · linarith only [hi, hij]
    · intro h
      apply dvd_of_eq
      linarith only [h]


  -- Therefore, a pair $(n,k)$ is a solution if and only if $n + 2k = 66$.
  have p_in_s_iff {p} (hp : p ∈ t) : p ∈ s ↔ 66 = p.1 + 2 * p.2 := by
    simp [hs, hp]
    simp [ht] at hp
    rw [sixty_seven_dvd_a_iff hp.1.1 hp.2]

  -- This means that $s$ is actually the set of $(n,k)$ such that $n + 2k = 66$, $n < 50$, and $n +
  -- k < 50$.
  replace hs : s = {p ∈ t | 66 = p.1 + 2 * p.2} := by
    ext p
    simp [hs, ht]
    intro h1 _ h2
    rw [sixty_seven_dvd_a_iff h1 h2]

  -- We will analyze the sitution row-by-row. Let $s_i'$ be the elements of $s$ in the $i$th row.
  let s' (i : ℕ) := {p ∈ s | p.1 = i}

  -- Then, $s$ is just the union of all $s_i'$ where $i < 50$.
  have s_union_rows : s = (range 50).biUnion s' := by
    ext p
    simp [s', hs, ht]
    intro h _ _ _
    exact h

  -- Moreover, because each $s_i'$ is a separate row, they are disjoint, so the cardinality of
  -- $s$ is the sum of the cardinalities of the $s_i'$.
  have s_card_eq_sum_s'_card : s.card = ∑ i ∈ range 50, (s' i).card := by
    rw [s_union_rows, card_biUnion]
    intro i1 hi1 i2 hi2 hi1i2
    rw [Finset.disjoint_iff_ne]
    intro j1 hj1 j2 hj2 hj1j2
    apply hi1i2
    simp [s'] at hj1 hj2
    rw [←hj1.2, ←hj2.2, hj1j2]

  -- Notice that each row contain at most one element such that $n + 2k = 66$.
  have s'_card_le_one (i) : (s' i).card ≤ 1 := by
    -- To see this, let $(i,j)$ and $(i,j')$ be two elements in $s_i$ such that $i + 2j = i + 2j' =
    -- 66$.
    rw [Finset.card_le_one]
    intro ⟨i, j⟩ h ⟨i, j'⟩ h'
    simp [s', hs] at h h'
    rcases h with ⟨⟨_, h⟩, rfl⟩
    rcases h' with ⟨⟨_, h'⟩, rfl⟩
    simp
    -- But then, $2j = 2j'$, so $j = j'$.
    linarith only [h, h']

  -- Therefore, the cardinality of $s$ just the number of rows that contain an element such that $n
  -- + 2k = 66$.
  have s_card_eq_s'_nonempty_card : s.card = {i ∈ range 50 | (s' i).Nonempty}.card := by
    rw [s_card_eq_sum_s'_card]

    let a := {i ∈ range 50 | (s' i).card = 0}
    let b := {i ∈ range 50 | (s' i).card = 1}

    have : range 50 = a ∪ b := by
      ext i
      simp [-card_eq_zero]
      constructor
      · intro h
        simp [a, b, -card_eq_zero]
        have : (s' i).card ≤ 1 := s'_card_le_one i
        interval_cases (s' i).card <;> simp [h]
      · simp [a, b]
        rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    rw [this]

    have : Disjoint a b := by
      rw [Finset.disjoint_iff_ne]
      rintro i hi j hj rfl
      simp [a, b, -card_eq_zero] at hi hj
      replace hi := hi.2
      replace hj := hj.2
      rw [hi] at hj
      contradiction
    rw [sum_union this]

    have : ∑ i ∈ a, (s' i).card = 0 := by
      symm
      calc _ = ∑ i ∈ a, 0 := by simp
           _ = _ := ?_
      apply sum_congr; rfl
      intro i hi
      simp [a, -card_eq_zero] at hi
      rw [hi.2]
    rw [this, zero_add]

    have : ∑ i ∈ b, (s' i).card = b.card := by
      symm
      calc _ = ∑ i ∈ b, 1 := by simp
           _ = _ := ?_
      apply sum_congr; rfl
      intro i hi
      simp [b] at hi
      rw [hi.2]
    rw [this]

    congr
    ext i
    simp [a, b]
    constructor
    · rintro ⟨hi, hs'i⟩
      split_ands
      · right
        exact ⟨hi, hs'i⟩
      · rw [←Finset.one_le_card]
        rw [←hs'i]
    · rintro ⟨(⟨hi, hs'i1⟩ | ⟨hi, hs'i1⟩), hs'i2⟩
      · rw [←card_eq_zero] at hs'i1
        rw [←one_le_card] at hs'i2
        rw [hs'i1] at hs'i2
        contradiction
      · exact ⟨hi, hs'i1⟩

  -- Let's when a row contains an element such that $n + 2k = 66$. We claim that $i$th row contains
  -- such an element if and only if $i$ is even and $i \le 33$.
  have s'_nonempty_iff {i : ℕ} (hi : i ∈ range 50) : (s' i).Nonempty ↔ Even i ∧ i ≤ 33 := by
    constructor
    -- To see this, let $i < 50$. Assume that $s_i'$ is nonempty. Let $(i, j) \in s_i'$.
    · rintro ⟨⟨i, j⟩, hij⟩
      simp [s', hs, ht] at hij hi
      -- Then, $i + 2j = 66$, $i < 50$ and $i + j < 50$.
      rcases hij with ⟨⟨⟨⟨_, hj⟩, hij1⟩, hij2⟩, rfl⟩
      split_ands
      -- Because all terms except $i$ in the equation $i + 2j = 66$ are even, $i$ must be even.
      · rw [even_iff_two_dvd]
        zify at hij2 ⊢
        use (33:ℤ) - j
        linarith only [hij2]
      -- And the inequalities $i < 50$, $j < 50$, $i + j < 50$ imply that $i \le 33$.
      · omega
    -- For the converse, let $i$ be even and $i \le 33$. Then, $i + 2(33 - i) = 66$.
    · intro ⟨hi1, hi2⟩
      -- Write, $i = 2j$.
      rcases hi1 with ⟨j, hij⟩
      replace hij : i = 2 * j := by linarith only [hij]
      use ⟨i, 33 - j⟩
      simp [s', hs, ht]
      -- Then, it is easy to see that all conditions are satisfied.
      omega

  -- Then, combining the above two results, we see that the cardinality of $s$ is the number of even
  -- numbers less than or equal to $33$.
  have : s.card = {i ∈ range 50 | Even i ∧ i ≤ 33}.card := by
    rw [s_card_eq_s'_nonempty_card]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [s'_nonempty_iff hi]
  rw [this]

  -- These numbers are just $0, 2, 4, \ldots, 32$, so the answer is $17$.
  decide