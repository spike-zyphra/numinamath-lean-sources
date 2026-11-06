import Mathlib

open Nat Finset

/-- For each integer $n\geq 2$, let $S_n$ be the sum of all products $jk$, where $j$ and $k$ are
integers and $1 \leq j < k \leq n$. What is the sum of the 10 least values of $n$ such that $S_n$ is
divisible by $3$?

$\textbf{(A)}\ 196\qquad\textbf{(B)}\ 197\qquad\textbf{(C)}\ 198\qquad\textbf{(D)}\
199\qquad\textbf{(E)}\ 200$ -/
theorem number_theory_93405 (S : ℕ → ℕ) (A : ℕ → Finset (ℕ × ℕ))
    (hA : ∀ n, A n = {p ∈ Icc 1 n ×ˢ Icc 1 n | p.1 < p.2})
    (hS : ∀ n, S n = ∑ p ∈ (A n), p.1 * p.2) :
    ∑ i ∈ range 10, nth {n | 2 ≤ n ∧ S n % 3 = 0} i = 197 := by

  -- Let $A_n$ be the set of all pairs $(j,k)$ such that $1 \leq j < k \leq n$.
  -- Let $S_n$ be the sum of all products $jk$ where $p \in A_n$.
  -- We want to show that the sum of first 10 integers $n$ such that $2 \leq n$ and $S_n$ is
  -- divisible by $3$ is $197$.

  -- Notice, that as $n$ gets larger the sets $A_n$'s get larger as well.
  have hA_mono (n) : A n ⊆ A (n + 1) := by
    rintro ⟨i, j⟩ hij
    simp [hA] at hij ⊢
    omega

  -- For simplicity, let $B_n = A_{n+1} \setminus A_n$.
  let B n := A (n + 1) \ A n

  -- Clearly, $B_n = \{(i, n+1) \mid i \in [1, n]\}$.
  have hB (n) : B n = (Icc 1 n) ×ˢ {n + 1} := by
    ext ⟨i, j⟩
    constructor
    · intro hij
      simp [B, hA] at hij ⊢
      use i
      omega
    · intro hij
      simp [B, hA] at hij ⊢
      rcases hij with ⟨i, _, rfl, _⟩
      omega

  -- Then, we can write $S_{n+1} = S_n + \sum_{p \in B_n} p.1 \cdot p.2$.
  have hSB (n) : S (n + 1) = S n + ∑ p ∈ B n, p.1 * p.2 := by
    calc _ = ∑ p ∈ A (n + 1), p.1 * p.2 := by rw [hS]
         _ = ∑ p ∈ A n, p.1 * p.2 + ∑ p ∈ B n, p.1 * p.2 := by rw [←Finset.sum_sdiff (hA_mono n)]; ring
         _ = _ := by rw [hS]

  -- The sum of the products of the pairs in $B_n$ is just $n \cdot (n+1)^2 / 2$. This is because
  -- the first components are just $1, 2, \ldots, n$ and the second components are all $n+1$.
  have hB_sum (n) : ∑ p ∈ B n, p.1 * p.2 = n * (n + 1)^2 / 2 := by
    calc _ = ∑ p ∈ (Icc 1 n) ×ˢ {n + 1}, p.1 * p.2 := by rw [hB]
         _ = ∑ i ∈ Icc 1 n, i * (n + 1) := by simp
         _ = (∑ i ∈ Icc 1 n, i) * (n + 1) := by rw [Finset.sum_mul]
         _ = (n * (n + 1) / 2) * (n + 1) := ?_
         _ = _ := ?_
    · congr
      suffices 2 * ∑ i ∈ Icc 1 n, i = n * (n + 1) from by omega
      induction' n with n ih
      · rfl
      · rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
        ring
    · apply_fun (fun x ↦ 2 * x);
      on_goal 2 => intro; simp
      dsimp
      rw [←mul_assoc, Nat.mul_div_cancel_left', Nat.mul_div_cancel_left']; ring
      · suffices (n * (n + 1)^2) % 2 = 0 by exact dvd_of_mod_eq_zero this
        rw [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.one_mod]
        have : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases this with (h | h) <;> simp [h]
      · suffices n * (n + 1) % 2 = 0 by exact dvd_of_mod_eq_zero this
        rw [Nat.mul_mod, Nat.add_mod]
        have : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases this with (h | h) <;> simp [h]

  -- Combining, we have $S_{n+1} = S_n + n \cdot (n+1)^2 / 2$.
  have hS' (n) : S (n + 1) = S n + n * (n + 1)^2 / 2 := by rw [hSB, hB_sum]

  -- Now, let's look at $S_n$ modulo $3$. The expression $n \cdot (n+1)^2 / 2$ is congruent to 0
  -- module 3 when $n$ is congruent to $0$ or $2$ modulo $3$. Moreover, it is is congruent to $2$
  -- modulo $3$ when $n$ is congruent to $1$ modulo $3$. This can be verified by direct computation.

  -- Therefore, $S_{n+1}$ is congruent to $S_n$ + 2 modulo $3$ when $n$ is congruent to $1$ modulo $3$.
  have hS_succ_mod_three {n} (h : n % 3 = 1) : S (n + 1) % 3 = (S n + 2) % 3 := by
    calc _ = (S n + n * (n + 1)^2 / 2) % 3 := by rw [hS']
         _ = ((S n) % 3 + (n * (n + 1)^2 / 2) % 3) % 3 := by exact add_mod (S n) _ 3
         _ = ((S n) % 3 + 2) % 3 := ?_
         _ = ((S n) % 3 + 2 % 3) % 3 := by rfl
         _ = (S n + 2) % 3 := by exact mod_add_mod (S n) 3 (2 % 3)

    rw [(?_ : (n * (n + 1)^2 / 2) % 3 = 2)]

    have : 2 ∣ n * (n + 1) := by
      suffices n * (n + 1) % 2 = 0 by exact dvd_of_mod_eq_zero this
      rw [Nat.mul_mod, Nat.add_mod, Nat.one_mod]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with (h | h) <;> simp [h]

    calc _ = ((n + 1) * (n * (n + 1))) / 2 % 3 := by congr 2; ring
         _ = (n + 1) * ((n * (n + 1)) / 2) % 3 := by congr 2; exact Nat.mul_div_assoc (n + 1) this
         _ = (((n + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
         _ = (((n % 3 + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
         _ = ((2 % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by rw [h]
         _ = (2 * ((n * (n + 1)) / 2)) % 3 := by simp
         _ = (n * (n + 1)) % 3 := by congr 1; exact Nat.mul_div_cancel' this
         _ = _ := by rw [Nat.mul_mod, Nat.add_mod, h]

  -- And, $S_{n+1}$ is congruent to $S_n$ modulo $3$ when $n$ is congruent to $0$ or $2$ modulo $3$.
  have hS_succ_mod_three' {n} (h : n % 3 ≠ 1) : S (n + 1) % 3 = S n % 3 := by
    have : n % 3 = 0 ∨ n % 3 = 2 := by omega

    calc _ = (S n + n * (n + 1)^2 / 2) % 3 := by rw [hS']
         _ = ((S n) % 3 + (n * (n + 1)^2 / 2) % 3) % 3 := by exact add_mod (S n) _ 3
         _ = ((S n) % 3 + 0) % 3 := ?_
         _ = ((S n) % 3 + 0 % 3) % 3 := by rfl
         _ = (S n + 0) % 3 := by exact mod_add_mod (S n) 3 (0 % 3)

    rw [(?_ : (n * (n + 1)^2 / 2) % 3 = 0)]

    have : 2 ∣ n * (n + 1) := by
      suffices n * (n + 1) % 2 = 0 by exact dvd_of_mod_eq_zero this
      rw [Nat.mul_mod, Nat.add_mod, Nat.one_mod]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with (h | h) <;> simp [h]

    have h : n % 3 = 0 ∨ n % 3 = 2 := by omega
    rcases h with (h | h)
    · calc _ = ((n + 1) * (n * (n + 1))) / 2 % 3 := by congr 2; ring
          _ = (n + 1) * ((n * (n + 1)) / 2) % 3 := by congr 2; exact Nat.mul_div_assoc (n + 1) this
          _ = (((n + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
          _ = (((n % 3 + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
          _ = (((0 + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by rw [h]
          _ = ((1 % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by rfl
          _ = ((n * (n + 1)) / 2) % 3 := by simp
          _ = _ := ?_

      have : 3 ∣ n := by exact dvd_of_mod_eq_zero h
      rcases this with ⟨k, rfl⟩

      have : 2 ∣ k * (3 * k + 1) := by
        suffices k * (3 * k + 1) % 2 = 0 by exact dvd_of_mod_eq_zero this
        rw [Nat.mul_mod]
        have : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases this with (h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod]

      calc _ = (3 * (k * (3 * k + 1)) / 2) % 3 := by congr 2; ring
           _ = 3 * ((k * (3 * k + 1)) / 2) % 3 := by congr 1; exact Nat.mul_div_assoc 3 this
           _ = _ := by simp

    · calc _ = ((n + 1) * (n * (n + 1))) / 2 % 3 := by congr 2; ring
           _ = (n + 1) * ((n * (n + 1)) / 2) % 3 := by congr 2; exact Nat.mul_div_assoc (n + 1) this
           _ = (((n + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
           _ = (((n % 3 + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by simp
           _ = (((2 + 1) % 3) * ((n * (n + 1)) / 2) % 3) % 3 := by rw [h]
           _ = _ := by simp

  -- So, the computation of $S_n$ modulo $3$ is simply starting from $S_2 = 2$, adding $2$ when $n$
  -- is congruent to $1$ modulo $3$, and keeping the same value when $n$ is congruent to $0$ or $2$
  -- This process repeats every $9$ steps. Because After 9 steps, $n$ hits 0, 1, 2 module 3 three
  -- times so we add three 2s which is 6 which is 0 module 3. Therefore, $S_{n + 9}$ is congruent to
  -- $S_n$ modulo $3$ for all $n$.
  have hS_add_nine_mod_three (n) : S (n + 9) % 3 = S n % 3 := by
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (h | h | h)
    all_goals {
      simp (discharger := omega) [hS_succ_mod_three', hS_succ_mod_three, add_mod]
      omega
    }

  -- This implies that $S_{9k + r}$ is congruent to $S_r$ modulo $3$ for all $k$ and $r$.
  have (k r) : S (9 * k + r) % 3 = S r % 3 := by
    induction' k with k ih
    · simp
    · calc _ = S ((9 * k + r) + 9) % 3 := by congr 2; ring
           _ = S (9 * k + r) % 3 := by rw [hS_add_nine_mod_three]
           _ = S r % 3 := by exact ih

  -- So, to compute $S_n$ modulo $3$, we only need to compute $S_{n \mod 9}$ modulo $3$.
  have hS_mod_three_eq_mod_nine_mod_three {n} : S n % 3 = S (n % 9) % 3 := by
    have hn : n = 9 * (n / 9) + n % 9 := by exact Eq.symm (div_add_mod n 9)
    nth_rw 1 [hn, this]

  -- Computing the first 10 values of $S_n$ modulo $3$ gives us the following sequence:
  -- 0 0 2 2 2 1 1 1 0 0 0 \dots

  let P (n : ℕ) := n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 8

  -- Because this pattern repeats every 9 steps, we see that $S_n$ is divisible by $3$ if and only
  -- if $n$ is congruent to $0$, $1$, or $8$ modulo $9$.
  have hS_mod_three_eq_zero_iff (n) : S n % 3 = 0 ↔ P n := by
    rw [hS_mod_three_eq_mod_nine_mod_three]
    have : n % 9 ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Set ℕ) := by
      simp; omega
    rcases this with (h | h | h | h | h | h | h | h | h)
    all_goals {
      simp [P]
      rw [h]
      try simp
      rw [hS, hA]
      decide
    }

  -- Now, with a simple computation we can find the first 10 values of $n$ such that $S_n$ is
  -- divisible by $3$. We just need to find the first 10 values of $n$ such that $2 \leq n$ and
  -- $n$ is congruent to $0$, $1$, or $8$ modulo $9$. This gives us the sequence $8, 9, 10, 17, 18,
  -- 19, 26, 27, 28, 35$.
  simp_rw [hS_mod_three_eq_zero_iff]
  let Q (n : ℕ) := 2 ≤ n ∧ P n
  show ∑ i ∈ range 10, nth {n | Q n} i = 197

  have infinite_setOf_Q : {n | Q n}.Infinite := by
    apply Set.Infinite.mono (s := (fun n ↦ 9 * n) '' Set.Ici 1)
    · rintro n ⟨m, hm, rfl⟩
      simp [Q, P]
      simp at hm
      linarith only [hm]
    · apply (Set.infinite_image_iff ?_).mpr
      · exact Set.Ici_infinite 1
      · intro; simp

  have nthQ_iff (n x : ℕ) :
      (Nat.nth Q n) = x ↔ (Nat.count Q x) ≤ n ∧ n < (Nat.count Q (x+1)) := by
    simp [←Finset.mem_Ico, Nat.lt_nth_iff_count_lt, Nat.count_le_iff_le_nth, infinite_setOf_Q]

  let inst (n x : ℕ) : Decidable (Nat.nth {n | Q n} n = x) :=
    decidable_of_iff' _ (nthQ_iff n x)

  let inst2 (n x : ℕ) : Decidable (x = Nat.nth {n | Q n} n) := by infer_instance

  rw [(by rfl : Finset.range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9})]
  simp

  suffices nth {n | Q n} 0 = 8  ∧ nth {n | Q n} 1 = 9  ∧ nth {n | Q n} 2 = 10 ∧
           nth {n | Q n} 3 = 17 ∧ nth {n | Q n} 4 = 18 ∧ nth {n | Q n} 5 = 19 ∧
           nth {n | Q n} 6 = 26 ∧ nth {n | Q n} 7 = 27 ∧ nth {n | Q n} 8 = 28 ∧
           nth {n | Q n} 9 = 35 from ?_
  · rcases this with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    norm_num

  decide