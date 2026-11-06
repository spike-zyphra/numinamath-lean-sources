import Mathlib

open Finset

/-- Let $1$; $4$; $7$; $\ldots$ and $9$; $16$; $23$; $\ldots$ be two arithmetic progressions. The
set $S$ is the union of the first $2004$ terms of each sequence. How many distinct numbers are in
$S$?

$\mathrm{(A) \ } 3722 \qquad \mathrm{(B) \ } 3732 \qquad \mathrm{(C) \ } 3914 \qquad
\mathrm{(D) \ } 3924 \qquad \mathrm{(E) \ } 4007$ -/
theorem number_theory_95435 {a b : ℕ → ℝ} (s : Finset ℝ) (ha : a 0 = 1 ∧ ∀ n, a (n + 1) = a n + 3)
    (hb : b 0 = 9 ∧ ∀ n, b (n + 1) = b n + 7)
    (hs : s = (image a (range 2004)) ∪ (image b (range 2004))) : s.card = 3722 := by

  -- Let $a$ and $b$ be the the arithmetic progressions $1, 4, \dots$ and $9, 16, \dots$ respectively.
  -- Let $s$ be the set of first 2004 terms of $a$ and $b$.
  -- We will show that $s$ has $3722$ elements.

  -- For simplicity, let $A$ be the set of the first 2004 terms of $a$ and $B$ be the set of the first
  -- 2004 terms of $b$.
  set A := image a (range 2004)
  set B := image b (range 2004)

  -- So that $s = A \cup B$. We know that $|s| = |A| + |B| - |A ∩ B|$.
  have hsAB : s.card = A.card + B.card - (A ∩ B).card := by
    have : (A ∩ B).card ≤ A.card + B.card := by
      calc _ ≤ A.card := by gcongr; simp
           _ ≤ _ := by simp
    zify [this]
    suffices s.card + (A ∩ B).card = A.card + B.card by omega
    rw [hs, Finset.card_union_add_card_inter]

  -- Therefore, it suffices to show that $|A| = 2004$, $|B| = 2004$, and $|A ∩ B| = 286$.
  suffices A.card = 2004 ∧ B.card = 2004 ∧ (A ∩ B).card = 286 by rw [hsAB, this.1, this.2.1, this.2.2]

  -- $A$ has 2004 elements. This is because $a$ is an arithmetic progression with a common difference of
  -- $3$ which is positive so it is strictly increasing sequence.
  have hasm : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [ha.2]
    linarith

  -- Likewise, $B$ has 2004 elements. This is because $b$ is an arithmetic progression with a common
  -- difference of $7$ which is positive so it is strictly increasing sequence.
  have hbsm : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hb.2]
    linarith

  refine ⟨?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    apply StrictMono.injective
    assumption
  · rw [card_image_of_injective, card_range]
    apply StrictMono.injective
    assumption

  -- Finally, let's show that $A$ and $B$ have $286$ elements in common.

  -- By definition, we can rewrite the set $A \cap B$ as $\{a n | n < 2004 \wedge \exists m < 2004,
  -- a n = b m\}
  -- Let $t$ be the set of all $n$ such that there exists an $m$ such that $a n = b m$.
  let t := {n ∈ range 2004 | ∃ m ∈ range 2004, a n = b m}
  have : A ∩ B = image a t := by aesop
  rw [this]

  -- Because $a$ is a strictly increasing sequence, we can instead show that $t$ has $286$ elements.
  rw [card_image_of_injective t (StrictMono.injective hasm)]

  -- At this point, we need to write down a general formula for the terms of $a$ and $b$.
  -- Because they are arithmetic progressions with known first terms and common differences, we can
  -- write down the $n$-th term of $a$ and $b$.
  -- We have $a n = 1 + 3n$ and $b n = 9 + 7n$.
  have han (n : ℕ) : a n = 1 + 3 * n := by
    induction' n with n ih
    · rw [ha.1]; norm_num
    · rw [ha.2, ih]
      push_cast
      ring
  have hbn (n : ℕ) : b n = 9 + 7 * n := by
    induction' n with n ih
    · rw [hb.1]; norm_num
    · rw [hb.2, ih]
      push_cast
      ring

  -- Using these formulas, we can write down $t$ as $\{n | n < 2004 \wedge \exists m < 2004, 3n = 8 + 7m\}$.
  have ht : t = {n ∈ range 2004 | ∃ m ∈ range 2004, 3 * n = 8 + 7 * m} := by
    ext n
    simp [t, han, hbn]
    intro hn
    constructor
    · rintro ⟨m, hm, hnm⟩
      refine ⟨m, hm, ?_⟩
      norm_cast at hnm
      omega
    · rintro ⟨m, hm, hnm⟩
      refine ⟨m, hm, ?_⟩
      norm_cast
      omega

  -- Let $u$ be the set of natural numbers less than 286.
  let u := range 286

  -- We claim that $u$ and $t$ are in a bijection via the map $f : k \mapsto 7 k + 5$.
  suffices u.card = t.card by rw [←this]; simp [u]

  apply Finset.card_bij (fun k _ ↦ 7 * k + 5)

  -- First, let's see that $f$ maps $u$ to $t$. Let $k$ be a natural number less than $286$.
  -- Then, $7k + 5$ is less than $2004$. Moreover, $3 k + 1$ is alos less than $2004$ and
  -- $3(7k + 5) = 21k + 15 = 8 + 7(3k + 1)$. Therefore, $7k + 5$ is in $t$.
  · intro k hk
    simp [u, ht] at hk ⊢
    refine ⟨by linarith, 3 * k + 1, by linarith, by ring⟩

  -- Next, let's see that $f$ is injective. This is very easy because addition and multiplication are
  -- injective operations.
  · intro k1 _ k2 _ h
    omega

  -- Finally, let's see that $f$ is surjective. Let $n$ be a natural number less than $2004$ such
  -- that $3n = 8 + 7m$ for some $m$ less than $2004$.
  · intro n hn
    simp [u, t] at hn ⊢
    rcases hn with ⟨hn, m, hm, hnm⟩
    rw [han, hbn] at hnm
    norm_cast at hnm
    have : 3 * n = 8 + 7 * m := by linarith

    -- We need to find $k < 286$ such that $7k + 5 = n$. Multiplying the equation $3n = 8 + 7m$ by
    -- $-2$ and then adding $7n$ to both sides, we get $n = 7 * (n - 2m - 3) + 5$.
    have : - 6 * (n:ℤ) = - 16 - 14 * m := by linarith
    have : (n:ℤ) = 7 * (n - 2 * m - 3) + 5 := by
      calc _ = 7 * (n:ℤ)  + (- 6 * n) := by ring
           _ = 7 * n - 16 - 14 * m := by rw [this]; ring
           _ = _ := by ring

    -- Therefore, let $k = n - 2m - 3$. We have $7k + 5 = n$. Moreover, $k < 286$.
    let k := n - 2 * m - 3
    refine ⟨k, by omega, by omega⟩