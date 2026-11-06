import Mathlib

open Nat Filter

/-- 2.16. (England, 70). For each value of $n \in \mathbf{N}$, denote by
    $a_{n} \in \mathbf{Z}^{+}$ the number of solutions to the equation
    \[ n^{2}+x^{2}=y^{2} \]
    in natural numbers greater than $n$.
    a) Prove that for any number $M$, the inequality $a_{n}>M$ holds for at least one value
    of $n \in \mathbf{N}$. -/
theorem number_theory_119616_1 {a : ℕ → ℕ∞}
    (ha : ∀ n, a n = {(x, y) | n ^ 2 + x ^ 2 = y ^ 2 ∧ x > n ∧ y > n}.encard) :
    ∀ M : ℕ, ∃ n > 0, a n > M := by
  -- Replace the conclusion $a_n > M$ with $a_n \geq M$ to facilitate the proof.
  suffices ∀ M : ℕ, ∃ n > 0, a n ≥ M by
    intro M
    obtain ⟨n, n_pos, hn⟩ := this (M + 1)
    rw [cast_add, cast_one, ge_iff_le, ENat.add_one_le_iff (by simp)] at hn
    exact ⟨n, n_pos, hn⟩
  -- As in the problem's solution, prove that for any $l$, $3 ^ l$ satisfies the conclusion,
  -- i.e., $a_{3 ^ l} \geq l$ (in fact, equality holds).
  intro l
  refine ⟨3 ^ l, by simp, ?_⟩
  simp only [ha]
  conv_rhs => rw [← Finset.card_range l, ← Set.encard_coe_eq_coe_finsetCard]
  apply Function.Embedding.encard_le
  -- Now, we only need to show that there is an injection from the set $\{0, \cdots, l - 1\}$
  -- to the given set $\{(x, y) | n ^ 2 + x ^ 2 = y ^ 2, x, y \geq n\}$, thereby proving that
  -- the cardinality of this set is at least $l$. We explicitly construct this injection by
  -- mapping $i$ to $(x_i, y_i)$.
  let x i := (3 ^ (2 * l - i) - 3 ^ i) / 2
  let y i := (3 ^ (2 * l - i) + 3 ^ i) / 2
  -- Prove some properties of $x_i$ and $y_i$. First, $x_i \leq y_i$.
  have x_le_y {i} : x i ≤ y i := by
    simpa only [x, y] using Nat.div_le_div_right ((sub_le _ _).trans (by simp))
  -- A lemma: If $i < l$, then $3 ^ i \leq 3 ^ {2l - i}$. This will be repeatedly used in
  -- the following proofs.
  have pow_le {i} (hi : i < l) : 3 ^ i ≤ 3 ^ (2 * l - i) :=
    pow_le_pow_of_le_right (by norm_num) (by omega)
  -- $x_i$ is indeed an integer, meaning the division in the definition is mathematical division
  -- rather than truncating division. That is, $2$ divides $3 ^ (2l - i) - 3 ^ i$.
  have x_int {i} (hi : i < l) : 2 ∣ 3 ^ (2 * l - i) - 3 ^ i := by
    simp [← even_iff_two_dvd, even_sub, even_pow, pow_le hi,
      show Odd 3 from odd_two_mul_add_one 1]
  -- $y_i$ is indeed an integer in the mathematical sense, similar to the previous lemma.
  have y_int {i} : 2 ∣ 3 ^ (2 * l - i) + 3 ^ i := by
    simp [← even_iff_two_dvd, even_add, even_pow,
      show Odd 3 from odd_two_mul_add_one 1]
  -- $y_i + x_i$ equals $3 ^ {2l - i}$.
  have y_add_x {i} (hi : i < l) : y i + x i = 3 ^ (2 * l - i) := by
    simp only [x, y, ← Nat.add_div_of_dvd_right y_int]
    convert_to 2 * 3 ^ (2 * l - i) / 2 = _ using 2
    · specialize pow_le hi
      omega
    · simp
  -- $y_i - x_i$ equals $3 ^ i$. These two lemmas will be substituted into the difference
  -- of squares formula to compute $y_i ^ 2 - x_i ^ 2$.
  have y_sub_x {i} (hi : i < l) : y i - x i = 3 ^ i := by
    convert_to _ = 2 * 3 ^ i / 2
    · simp
    · apply Nat.sub_eq_of_eq_add
      simp only [x, y]
      rw [← Nat.add_div_of_dvd_right (by simp)]
      congr 1
      specialize pow_le hi
      omega
  -- Now, prove that the mapping $i \mapsto (x_i, y_i)$ is indeed an injective function
  -- satisfying the conditions.
  refine ⟨fun | ⟨i, hi⟩ => ⟨(x i, y i), ?_⟩, ?_⟩
  · -- Simplify the hypotheses and the goal, and specialize the lemmas `y_add_x`, `y_sub_x`,
    -- and `x_int` to $i$ so that `omega` can automatically find them.
    simp at hi ⊢
    specialize y_add_x hi
    specialize y_sub_x hi
    specialize x_int hi
    -- Note that the third goal can be easily derived from the second goal.
    refine ⟨?_, ?lt, lt_of_lt_of_le ?lt x_le_y⟩
    · -- Prove the equality holds, i.e., $(3 ^ l) ^ 2 + x_i ^ 2 = y_i ^ 2$, using the
      -- difference of squares formula `Nat.sq_sub_sq`.
      rw [Nat.Simproc.add_eq_le]
      · rw [Nat.sq_sub_sq, y_add_x, y_sub_x, ← pow_mul, ← pow_add]
        congr 1
        omega
      · rw [Nat.pow_le_pow_iff_left (by simp)]
        exact x_le_y
    · -- Prove $3 ^ l < x_i$.
      simp only [x, Nat.lt_div_iff_mul_lt' x_int]
      -- We only need to show $2 \cdot 3 ^ l < 3 ^ {2l - i} - 3 ^ i$, and since $i < l$,
      -- we have $2 \cdot 3 ^ l = 3 ^ {l + 1} - 3 ^ l < 3 ^ {l + 1} - 3 ^ {l - 1} \leq
      -- 3 ^ {2l - i} - 3 ^ i$.
      calc
        _ = 3 ^ (2 * l - (l - 1)) - 3 ^ l := by
          rw [show 2 * l - (l - 1) = l + 1 by omega]
          omega
        _ < 3 ^ (2 * l - (l - 1)) - 3 ^ (l - 1) := by
          have : 3 ^ (l - 1) < 3 ^ l := Nat.pow_lt_pow_of_lt (by omega) (by omega)
          have : 3 ^ l ≤ 3 ^ (2 * l - (l - 1)) := Nat.pow_le_pow_of_le_right (by omega) (by omega)
          omega
        _ ≤ 3 ^ (2 * l - i) - 3 ^ (l - 1) :=
          Nat.sub_le_sub_right (Nat.pow_le_pow_of_le_right (by omega) (by omega)) _
        _ ≤ _ :=
          Nat.sub_le_sub_left (Nat.pow_le_pow_of_le_right (by omega) (by omega)) _
  · -- Prove that our mapping is injective. If $x_i = x_j, y_i = y_j$, then
    -- $y_i - x_i = y_j - x_j$, i.e., $3 ^ i = 3 ^ j$, which implies $i = j$.
    simp [Function.Injective]
    intro i hi j hj eq_x eq_y
    have : (?_ - ?_ : ℕ) = ?_ - ?_ := by congr 1; exact eq_y; exact eq_x
    rw [y_sub_x hi, y_sub_x hj] at this
    simpa using this

/-- 2.16. (England, 70). For each value of $n \in \mathbf{N}$, denote by
    $a_{n} \in \mathbf{Z}^{+}$ the number of solutions to the equation
    \[ n^{2}+x^{2}=y^{2} \]
    in natural numbers greater than $n$.
    b) Is it true that lim $a_{n}=\infty$? -/
theorem number_theory_119616_2 {a : ℕ → ℕ∞}
    (ha : ∀ n, a n = {(x, y) | n ^ 2 + x ^ 2 = y ^ 2 ∧ x > n ∧ y > n}.encard) :
    ¬Tendsto a atTop atTop := by
  -- If the function $a$ tends to infinity, then the subsequence $a_2, a_3, a_5, \cdots$
  -- at prime indices would also tend to infinity.
  intro h
  replace h := h.comp <| tendsto_atTop_atTop_of_monotone
    (nth_monotone infinite_setOf_prime)
    (fun n => ⟨n, le_nth fun hfin => absurd hfin infinite_setOf_prime⟩)
  -- Use `tendsto_atTop_atTop` to rewrite "tends to infinity" to an arithmetic statement.
  rw [tendsto_atTop_atTop] at h
  -- However, the subsequence $a_2, a_3, a_5, \cdots$ at prime indices cannot tend to infinity
  -- because for any prime $p$, $a_p \leq 3$. We only need to prove this fact; hence, we use the
  -- `absurd` tactic to replace the goal with it.
  absurd h
  clear h
  simp only [Function.comp_apply, not_forall, not_exists, not_le]
  refine ⟨4, fun n => ⟨n, by rfl, ?_⟩⟩
  -- Now we only need to prove: For any $n$, let $p$ be the $n$-th prime (starting from 0),
  -- then $a_p < 4$.
  let p := nth Nat.Prime n
  suffices a p ≤ 3 from lt_of_le_of_lt this (by norm_num)
  -- That is, $a_p ≤ 3$. We prove that $a_p$ is less than or equal to the cardinality of the set
  -- of factor pairs of $p ^ 2$, i.e., $\{(x, y) | xy = p ^ 2\}$, represented in Lean as
  -- `Nat.divisorsAntidiagonal`.
  transitivity (p ^ 2).divisorsAntidiagonal.toSet.encard
  · -- We only need to show the existence of certain injective map.
    simp only [ha]
    apply Function.Embedding.encard_le
    -- An obvious lemma that will be used repeatedly in the following proof.
    have le_of_eqn {x y : ℕ} (h : p ^ 2 + x ^ 2 = y ^ 2) : x ≤ y := by
      rw [← Nat.pow_le_pow_iff_left (show 2 ≠ 0 by simp), ← h]
      simp
    -- Map the solution $(x, y)$ of the original equation to $(y + x, y - x)$.
    refine ⟨fun | ⟨⟨x, y⟩, hxy⟩ => ⟨(y + x, y - x), ?_⟩, ?_⟩
    · -- Since $(y + x)(y - x) = y ^ 2 - x ^ 2 = p ^ 2$, $(y + x, y - x)$ is indeed
      -- a factor pair of $p ^ 2$.
      simp at hxy ⊢
      refine ⟨?_, (prime_nth_prime _).ne_zero⟩
      zify
      rw [cast_sub (le_of_eqn hxy.1)]
      ring_nf
      zify at hxy
      rw [← hxy.1]
      ring
    · -- Prove that the mapping $(x, y) \mapsto (x + y, x - y)$ is injective; this can be done
      -- by transferring it to $\mathbb{Z}$ and using the `linarith` tactic.
      rintro ⟨⟨x, y⟩, hxy⟩ ⟨⟨x', y'⟩, hx'y'⟩
      simp
      simp at hxy hx'y'
      zify
      intro h h'
      rw [cast_sub (le_of_eqn hxy.1), cast_sub (le_of_eqn hx'y'.1)] at h'
      constructor <;> linarith
  · -- Prove that the set of factor pairs of $p ^ 2$ has exactly 3 elements.
    rw [Set.encard_coe_eq_coe_finsetCard, cast_le_ofNat,
      ← map_div_left_divisors, Finset.card_map, ← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow (prime_nth_prime _)]
