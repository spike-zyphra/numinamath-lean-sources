import Mathlib

open Finset

/- Let $M$ be a set of positive integers with the following three properties:

(1) $2018 \in M$.

(2) If $m \in M$, then all positive divisors of $m$ are also elements of $M$.

(3) For all elements $k, m \in M$ with $1 < k < m$, $km + 1$ is also an element of $M$.

Prove that $M = \mathbb{Z}_{\geq 1}$. -/

theorem number_theory_259954 (M : Set ℕ) (h1 : ∀ m ∈ M, 0 < m)
    (h2 : 2018 ∈ M) (h3 : ∀ m ∈ M, ∀ d ∈ Nat.divisors m, d ∈ M)
    (h4 : ∀ k m : ℕ, k ∈ M → m ∈ M → 1 < k → k < m → (k * m + 1) ∈ M) :
    M = {x | 1 ≤ x} := by

    ext x
    constructor

    -- the forward direction
    .
      intro h
      specialize h1 x h
      simp
      omega

    -- the backward direction
    intro hx
    simp at hx

    -- it suffices to show that {1, 2, ..., l} ⊆ M for all 5 ≤ l
    suffices f: ∀ l, 5 ≤ l → ∀ y, 0 < y ∧ y ≤ l → y ∈ M by
      specialize f (x + 5) (by omega) x (by omega)
      tauto

    -- then we prove this by induction

    -- we first show that 1, 2, 3, 4, 5 are in M
    have f1: 1 ∈ M := by
      specialize h3 2018 (by tauto)
      specialize h3 1 (by decide)
      tauto
    have f2: 2 ∈ M := by
      specialize h3 2018 (by tauto)
      specialize h3 2 (by decide)
      tauto
    have f2019: 2019 ∈ M := by
      have f': 1009 ∈ M := by
        specialize h3 2018 (by tauto)
        specialize h3 1009 (by simp; norm_num)
        tauto
      specialize h4 2 1009 (by tauto) (by tauto) (by norm_num) (by norm_num)
      simp at h4
      tauto
    have f3: 3 ∈ M := by
      specialize h3 2019 (by tauto)
      specialize h3 3 (by simp; norm_num)
      tauto
    have f2020: 2020 ∈ M := by
      have f': 673 ∈ M := by
        specialize h3 2019 (by tauto)
        specialize h3 673 (by simp; norm_num)
        tauto
      specialize h4 3 673 (by tauto) (by tauto) (by norm_num) (by norm_num)
      simp at h4
      tauto
    have f4: 4 ∈ M := by
      specialize h3 2020 (by tauto)
      specialize h3 4 (by simp; norm_num)
      tauto
    have f5: 5 ∈ M := by
      specialize h3 2020 (by tauto)
      specialize h3 5 (by simp; norm_num)
      tauto
    clear f2019 f2020
    intro l hl
    induction' l with l ih
    .
      norm_num at hl
    .
      -- case when l = 4
      by_cases r: l = 4
      .
        intro y hy
        simp [r] at hy
        rcases hy with ⟨p, q⟩
        interval_cases y
        all_goals tauto
      -- case when 5 ≤ l
      .
        replace hl: 5 ≤ l := by
          clear *- hl r
          omega
        simp [hl] at ih

        -- it suffices to show that l+1 ∈ M
        suffices l + 1 ∈ M by
          intro y hy
          by_cases u: y ≤ l
          .
            specialize ih y (by omega) (by omega)
            tauto
          .
            replace u: y = l + 1 := by
              clear *- hy u
              omega
            rw [u]
            tauto
        clear r h2 h1
        have il:= ih l (by omega) (by omega)
        by_cases o: Even l

        -- case when l is even
        .
          rw [even_iff_exists_two_mul] at o
          obtain ⟨b, o⟩ := o
          have v: b ∈ M := by
            specialize h3 l il
            specialize h3 b (by simp [o]; omega)
            tauto
          specialize h4 2 b (by tauto) (by tauto) (by omega) (by omega)
          rw [← o] at h4
          tauto

        -- case when l is odd
        .
          simp at o

          -- we show that l + 2 ∈ M
          have c: l + 2 ∈ M := by
            apply Odd.exists_bit1 at o
            obtain ⟨b, o⟩ := o
            have i: b + 1 ∈ M := by
              specialize ih (b + 1) (by omega) (by omega)
              tauto
            specialize h4 2 (b + 1) (by tauto) (by tauto) (by omega) (by omega)
            rw [show 2 * (b + 1) + 1 = l + 2 by omega] at h4
            exact h4

          -- then (l + 1) ^ 2 is in M
          specialize h4 l (l + 2) (by tauto) (by tauto) (by omega) (by omega)
          rw [show l * (l + 2) + 1 = (l + 1) * (l + 1) by ring] at h4
          specialize h3 ((l + 1) * (l + 1)) (by tauto)
          specialize h3 (l + 1) (by simp)
          exact h3
          