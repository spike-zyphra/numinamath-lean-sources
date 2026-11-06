import Mathlib

open Finset Classical

/- (25 points) (1) First, select $n$ numbers from $1, 2, \cdots, 2020$, then choose
  any two numbers $a$ and $b$ from these $n$ numbers, such that $a \nmid b$. Find
  the maximum value of $n$. -/
theorem number_theory_291025 :
    IsGreatest {n : ℕ | ∃ S ∈ (Icc 1 2020).powersetCard n,
      S.toSet.Pairwise (¬· ∣ ·)} 1010 := by
  constructor
  · /- $n = 1010$ satisfies the condition: Consider the sequence $1011, \cdots, 2020$,
      then any distinct elements does not divides each other. -/
    use Icc 1011 2020
    simp
    constructor
    · /- The sequence $1011, \cdots, 2020$ is contained in the interval $[1011, 2020]$. -/
      intro x
      simp
      omega
    · /- For any $x, y$ satisfies $1011 \leq x \leq 2020$, we have both $x \nmid y$
        and $y \nmid x$. -/
      intro x hx y hy ne ⟨k, y_eq⟩
      /- From $x > 1010$, we have $2x > 2020$, so $y = kx \geq 2x > 2020$,
        which derives a contradiction. -/
      have : 2020 < y := calc
        _ = 1010 * 2 := rfl
        _ < x * 2 := by
          refine Nat.mul_lt_mul_of_pos_right ?_ (by simp)
          simp at hx
          omega
        _ ≤ y := by
          /- Since $k \neq 0$ and $k \neq 1$, we have $k \geq 2$, so $2x \leq y$. -/
          rw [y_eq]
          apply Nat.mul_le_mul_left
          suffices k ≠ 0 ∧ k ≠ 1 by omega
          refine ⟨fun eq => ?_, fun eq => ?_⟩ <;> cases eq
          · simp [y_eq] at hy
          · simp [y_eq] at ne
      simp at hy
      omega
  · /- We use the symbol $N$ to represent the number $1010$. If we don't replace these
      large numbers by local hypotheses, some tactics (such as `congr` and `assumption`)
      may fail after excessively deep recursion. -/
    set N := 1010 with N_def
    rw [show 2020 = 2 * N from rfl]
    clear_value N
    /- Define the sets $A_i$. -/
    let A i := (Icc 1 (2 * N)).filter fun x => ∃ k, x = (2 * i + 1) * 2 ^ k
    simp [upperBounds, Set.Pairwise, not_imp_not]
    intro n S hS hcard ndvd
    by_contra n_gt
    simp at n_gt
    /- Prove that the set $S$ intersects with some $A_i$ with at least two elements. -/
    have : ∃ i ∈ range N, 1 < #(S ∩ A i) := by
      /- We prove that these $S \cap A_i$ (indeed, $A_i$) are pairwisely disjoint. -/
      have disj : Set.PairwiseDisjoint (range N) fun i => S ∩ A i := by
        rintro i - j - ne
        simp [A, disjoint_iff_ne]
        rintro - - - - k₁ ⟨_⟩ - - - - k₂ ⟨_⟩ eq
        /- By computing the multiplicity, we can prove that the exponentials $k_1$ and $k_2$
          are equal, so $i$ is equal to $j$. -/
        have emul_eq := congr_arg (emultiplicity 2) eq
        simp only [
          Nat.Prime.emultiplicity_mul Nat.prime_two,
          Nat.Prime.emultiplicity_pow_self Nat.prime_two,
          emultiplicity_eq_zero.mpr (Nat.not_two_dvd_bit1 _),
          zero_add, Nat.cast_inj
        ] at emul_eq
        subst emul_eq
        rw [Nat.mul_right_cancel_iff (by simp)] at eq
        omega
      /- Assuming that for any $i$, `#(S ∩ A i) ≤ 1`, then the sum of `#(S ∩ A i)` will
        less or equal than $N$. However, it's not possible: the union of these `S ∩ A i`
        is equal to $S$, and `#S = n > N`. -/
      by_contra h
      simp only [not_exists, not_and, not_lt] at h
      replace h := sum_le_sum h
      simp at h
      /- We can convert the sum of `#(S ∩ A i)` to the cardinality of the intersection
        of `S` and the union of all `A i`. -/
      rw [← card_disjiUnion _ _ disj, disjiUnion_eq_biUnion, ← Finset.inter_biUnion] at h
      rw [← hcard] at n_gt
      refine Nat.not_lt_of_le h ?_
      convert n_gt using 2
      rw [Finset.inter_eq_left]
      /- We only need to prove that $S$ is a subset of the union of all $A_i$.
        We fix a $x \in S$ and prove that $x$ is indeed in some $A_i$. -/
      intro x hx
      /- we can factor $x$ as `i' * 2 ^ multiplicity 2 x`, where `i'` is not divisible by $2$. -/
      have fin_mul : FiniteMultiplicity 2 x := by
        rw [Nat.finiteMultiplicity_iff]
        have := hS hx
        simp at this
        omega
      obtain ⟨i', x_eq, odd⟩ := fin_mul.exists_eq_pow_mul_and_not_dvd
      /- Since `i'` is not divisible by $2$, we can obtain an `i` such that `i' = 2 * i + 1`. -/
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd] at odd
      obtain ⟨i, ⟨_⟩⟩ := odd
      simp only [mem_biUnion, mem_range, mem_filter, A]
      /- We can prove that $x \in A_i$, with the exponent `multiplicity 2 x`. -/
      refine ⟨i, ?_, hS hx, multiplicity 2 x, by rwa [mul_comm]⟩
      /- Then some elementary arithmetic finishes the proof. -/
      suffices 2 * i + 1 ≤ 2 * N by omega
      calc
        _ ≤ x := by
          rw [x_eq]
          simp [Nat.one_le_two_pow]
        _ ≤ 2 * N := by
          have := hS hx
          simp only [mem_Icc] at this
          exact this.2
    /- We can find an $i$ such that $S \cap A_i$ has at least two elements.
      Assuming that the two elements be $x$ and $y$, we can derive a contradiction. -/
    simp only [one_lt_card] at this
    obtain ⟨i, hi, x, hx, y, hy, ne⟩ := this
    simp [A, mem_inter] at hx hy
    /- Since $x$ and $y$ are elements of $A_i$, we can assume that $x = (2i + 1) 2^{k_1}$
      and $y = (2i + 1) 2^{k_2}$. -/
    obtain ⟨k₁, ⟨_⟩⟩ := hx.2.2
    obtain ⟨k₂, ⟨_⟩⟩ := hy.2.2
    replace hx := hx.1
    replace hy := hy.1
    /- Since $x \neq y$ (the two elements are distinct), we have $k_1 \neq k_2$. -/
    have k_ne := ne
    simp at k_ne
    cases' Nat.lt_or_lt_of_ne k_ne with lt gt
    · /- If $k_1 < k_2$, we have $x \mid y$, so $x = y$. -/
      exact ne (ndvd hx hy <| Nat.mul_dvd_mul_left _ <| Nat.pow_dvd_pow _ <| le_of_lt lt)
    · /- If $k_2 < k_1$, we have $y \mid x$, so $y = x$. -/
      exact ne (ndvd hy hx <| Nat.mul_dvd_mul_left _ <| Nat.pow_dvd_pow _ <| le_of_lt gt).symm
