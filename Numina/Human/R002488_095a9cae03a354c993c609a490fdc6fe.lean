import Mathlib

open Finset

/-- Consider the following $100$ sets of $10$ elements each: \begin{align*}
&\{1,2,3,\ldots,10\}, \\ &\{11,12,13,\ldots,20\},\\ &\{21,22,23,\ldots,30\},\\
&\vdots\\ &\{991,992,993,\ldots,1000\}. \end{align*} How many of these sets contain exactly two
multiples of $7$?

$\textbf{(A)}\ 40\qquad\textbf{(B)}\ 42\qquad\textbf{(C)}\ 43\qquad\textbf{(D)}\
49\qquad\textbf{(E)}\ 50$ -/
theorem number_theory_94142 {s : ℕ → Finset ℕ}
    (hs : ∀ k, s k = image (fun i ↦ 10 * k + i) (Icc 1 10)) :
    {k ∈ range 100 | {n ∈ s k | 7 ∣ n}.card = 2}.card = 42 := by

  -- Let $s_k$ be the set of numbers of the form $10i + 1$ for $i \in [1, 10]$.

  -- We divide $s_k$ into two sets $a_k$ and $b_k$. $a_k$ contains the first 7 elements of $s_k$
  -- and $b_k$ contains the last 3 elements of $s_k$.
  let a (k : ℕ) := image (fun i ↦ 10 * k + i) (Icc 1 7)
  let b (k : ℕ) := image (fun i ↦ 10 * k + i) (Icc 8 10)

  -- We have $s_k = a_k \cup b_k$.
  have s_eq_union_a_b (k) : s k = a k ∪ b k := by
    ext n
    simp [hs, a, b]
    constructor
    · intro h
      omega
    · intro h
      omega

  -- And, $a_k \cap b_k = \emptyset$.
  have disjoint_a_b (k) : Disjoint (a k) (b k) := by
    rw [Finset.disjoint_image]
    · exact disjoint_iff_inter_eq_empty.mpr rfl
    · intro i j
      simp_intro h

  -- Observe that $a_k$ contains 7 elements, so there exists exactly one element in $a_k$ that is
  -- divisible by 7.
  have a_filter_card (k) : {n ∈ a k | 7 ∣ n}.card = 1 := by
    apply le_antisymm
    · rw [Finset.card_le_one]
      simp [a]
      intro n hn1 hn2 hn3 m hm1 hm2 hm3
      omega
    · rw [Finset.one_le_card, Finset.filter_nonempty_iff]
      simp only [a, Finset.mem_image]
      use 10 * k + 1 + (6 * (10 * k + 1)) % 7
      constructor
      · use 1 + (6 * (10 * k + 1)) % 7
        simp
        omega
      · omega

  -- Because $b_k$ contains 3 elements, there can be at most 1 element in $b_k$ that is divisible by
  -- 7.
  have b_filter_card_le_one (k) : {n ∈ b k | 7 ∣ n}.card ≤ 1 := by
    rw [Finset.card_le_one]
    simp [b]
    intro n hn1 hn2 hn3 m hm1 hm2 hm3
    omega

  -- Therefore, the number of elements in $b_k$ that are divisible by 7 is exactyl 1 iff $b_k$
  -- contains an element that is divisible by 7.
  have b_filter_card_eq_one_iff (k) : {n ∈ b k | 7 ∣ n}.card = 1 ↔ {n ∈ b k | 7 ∣ n}.Nonempty := by
    constructor
    · intro h
      rw [←Finset.one_le_card, h]
    · intro h
      apply le_antisymm
      · apply b_filter_card_le_one
      · rwa [Finset.one_le_card]


  -- Therefore, $s_k$ contains exactly two elements that are divisible by 7 iff $b_k$ contains
  -- exactly one element that is divisible by 7.
  have s_filter_card_eq_two_iff (k) : {n ∈ s k | 7 ∣ n}.card = 2 ↔ ∃ n ∈ b k, 7 ∣ n := by
    rw [s_eq_union_a_b, Finset.filter_union, Finset.card_union_of_disjoint, a_filter_card]
    · constructor
      · intro h
        replace h : {n ∈ b k | 7 ∣ n}.card = 1 := by linarith
        rw [b_filter_card_eq_one_iff] at h
        rcases h with ⟨n, hn⟩
        use n
        simpa using hn
      · rintro ⟨n, hn⟩
        suffices {n ∈ b k | 7 ∣ n}.card = 1 by linarith
        rw [b_filter_card_eq_one_iff]
        use n
        simpa using hn
    · rw [Finset.disjoint_iff_inter_eq_empty, ←Finset.filter_inter_distrib]
      convert Finset.filter_empty _
      · rw [←Finset.disjoint_iff_inter_eq_empty]
        apply disjoint_a_b
      · infer_instance

  -- The elements of $b_k$ are $10k + 8$, $10k + 9$, and $10k + 10$, so $b_k$ contains an element
  -- that is divisible by 7 iff $10k + 8$, $10k + 9$, or $10k + 10$ is congruent to 0 modulo 7.
  have h8910 (k) : (∃ n ∈ b k, 7 ∣ n) ↔ (7 ∣ (10 * k + 8) ∨ 7 ∣ (10 * k + 9) ∨ 7 ∣ (10 * k + 10)) := by
    constructor
    · rintro ⟨n, hn1, hn2⟩
      simp [b] at hn1
      have : n = 10 * k + 8 ∨ n = 10 * k + 9 ∨ n = 10 * k + 10 := by omega
      rcases this with (rfl | rfl | rfl) <;> simp [hn2]
    · rintro (h | h | h)
      · use 10 * k + 8
        simp [b]
        omega
      · use 10 * k + 9
        simp [b]
        omega
      · use 10 * k + 10
        simp [b]
        omega

  -- With a simple modulo calculation, we can see that $10k + 8$ is divisible by 7 iff $k$ is congruent
  -- to 2 modulo 7.
  have h8 (k) : 7 ∣ (10 * k + 8) ↔ k % 7 = 2 := by
    constructor
    · intro h
      omega
    · intro h
      omega

  -- With a simple modulo calculation, we can see that $10k + 9$ is divisible by 7 iff $k$ is congruent
  -- to 4 modulo 7.
  have h9 (k) : 7 ∣ (10 * k + 9) ↔ k % 7 = 4 := by
    constructor
    · intro h
      omega
    · intro h
      omega

  -- With a simple modulo calculation, we can see that $10k + 10$ is divisible by 7 iff $k$ is congruent
  -- to 6 modulo 7.
  have h10 (k) : 7 ∣ (10 * k + 10) ↔ k % 7 = 6 := by
    constructor
    · intro h
      omega
    · intro h
      omega

  -- Therefore, combining everything, we have that $s_k$ contains exactly two elements that are
  -- divisible by 7 iff $k$ is congruent to 2, 4, or 6 modulo 7.
  replace s_filter_card_eq_two_iff (k) :
      {n ∈ s k | 7 ∣ n}.card = 2 ↔ k % 7 = 2 ∨ k % 7 = 4 ∨ k % 7 = 6 := by
    rw [s_filter_card_eq_two_iff, h8910, h8, h9, h10]

  -- In other words, the set of $k$ such that $s_k$ contains exactly two elements that are divisible
  -- by 7 is the set of $k$ such that $k$ is congruent to 2, 4, or 6 modulo 7.
  have : {k ∈ range 100 | {n ∈ s k | 7 ∣ n}.card = 2} = {k ∈ range 100 | k % 7 = 2 ∨ k % 7 = 4 ∨ k % 7 = 6} := by
    simp_rw [s_filter_card_eq_two_iff]
  rw [this]

  -- Now, two conclude, we need to find the number of $k$ in the range $[0, 99]$ such that $k$ is
  -- congruent to 2, 4, or 6 modulo 7.

  -- Let $a$ be the set of $k$ in the range $[0, 99]$ such that $k$ is congruent to 2, 4, or 6 modulo 7.
  -- Let $b$ be the set of $k$ in the range $[0, 99]$ such that $k$ is congruent to 2 modulo 7.
  -- Let $c$ be the set of $k$ in the range $[0, 99]$ such that $k$ is congruent to 4 modulo 7.
  -- Let $d$ be the set of $k$ in the range $[0, 99]$ such that $k$ is congruent to 6 modulo 7.
  set a := {k ∈ range 100 | k % 7 = 2 ∨ k % 7 = 4 ∨ k % 7 = 6}
  set b := {k ∈ range 100 | k % 7 = 2}
  set c := {k ∈ range 100 | k % 7 = 4}
  set d := {k ∈ range 100 | k % 7 = 6}

  -- Of course, $a = b \cup c \cup d$.
  have a_union : a = b ∪ c ∪ d := by
    ext k
    simp [a, b, c, d]
    tauto

  -- Moreover, $b, c, d$ are pairwise disjoint.
  have disjoint_b_c : Disjoint b c := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext k
    simp [b, c]
    omega
  have disjoint_c_d : Disjoint c d := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext k
    simp [c, d]
    omega
  have disjoint_b_d : Disjoint b d := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext k
    simp [b, d]
    omega

  -- Therefore, it suffices to show that $b$, $c$, $d$ have 14 elements.
  suffices b.card = 14 ∧ c.card = 14 ∧ d.card = 14 by
    rw [a_union, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, this.1, this.2.1, this.2.2]
    · exact disjoint_b_c
    · rw [Finset.disjoint_union_left]
      exact ⟨disjoint_b_d, disjoint_c_d⟩

  -- However, we know that these all contain $\lfloor 100 / 7 \rfloor$ elements.
  split_ands <;> decide