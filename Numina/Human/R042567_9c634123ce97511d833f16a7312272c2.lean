import Mathlib

open Finset

/- Let $n(n \geq 1)$ be a positive integer and $U=\{1, \ldots, n\}$. Let $S$ be a nonempty subset of $U$ and let $d(d \neq 1)$ be the smallest common divisor of all elements of the set $S$. Find the smallest positive integer $k$ such that for any subset $T$ of $U$, consisting of $k$ elements, with $S \subset T$, the greatest common divisor of all elements of $T$ is equal to 1 . -/
theorem number_theory_605977 (n d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 n)
(Sne : S.Nonempty) (lcd : IsLeast {d' | d' ≠ 1 ∧ ∀ l ∈ S, d' ∣ l} d) :
IsLeast {k | S.card ≤ k ∧ ∀ T ⊆ Icc 1 n, S ⊆ T → T.card = k → T.val.gcd = 1} (1 + n / d) := by
-- Rewrite the goal and the assumption lcd
  rw [IsLeast, lowerBounds] at *; simp; simp at lcd; rcases lcd with ⟨⟨dne, hdvd⟩, lcd⟩
  rcases Sne with ⟨r, hr⟩; simp [subset_iff] at hS; have rbd := hS hr
-- Prove that $d$ is greater than or equal to $2$
  have dge : 2 ≤ d := by
    specialize hdvd r hr; by_contra!; interval_cases d
    · simp at hdvd; omega
    contradiction
-- Prove that $d$ is prime
  have dpr : d.Prime := by
    rw [Nat.prime_def]; constructor; exact dge
    intro m mdvd; by_cases hm : m = 1; left; exact hm
    right; rw [Nat.eq_iff_le_and_ge]; constructor
    · apply Nat.le_of_dvd; omega; exact mdvd
    apply lcd; exact hm; intro l hl; apply dvd_trans mdvd; exact hdvd l hl
-- Prove that $S$ is containded in the subset of all multiples of $d$ in $[1, n]$
  have Ssubs : S ⊆ filter (fun i => d ∣ i) (Icc 1 n) := by
    simp [subset_iff]; intro m hm; constructor; exact hS hm; exact hdvd m hm
  split_ands
  · apply card_le_card at Ssubs; rw [Nat.Icc_succ_left, Nat.Ioc_filter_dvd_card_eq_div] at Ssubs; omega
  -- To prove the main goal, we first show that if $T$ is a subset of $[1, n]$ containing $S$ with cardinality $1+n/d$
  -- then the greatest common divisor of $T$ has to be $1$. We proceed by contradiction
  · intro T Tsubs hT Tcard; simp [subset_iff] at hT Tsubs; by_contra h
  -- Prove that the gcd of $T$ is positive and less than or equal to $n$
    have gcdbd : 0 < T.val.gcd ∧ T.val.gcd ≤ n := by
      have : T.val.gcd ∣ r := by apply Multiset.gcd_dvd; simp; exact hT hr
      constructor
      · apply Nat.pos_of_dvd_of_pos this; omega
      apply le_trans _ rbd.right; apply Nat.le_of_dvd; omega; exact this
  -- Prove that $T$ is a subset of the set of all multiples of $T.val.gcd$ in $[1, n]$
    have : T ⊆ filter (fun i => T.val.gcd ∣ i) (Icc 1 n) := by
      simp [subset_iff]; intro i hi; constructor
      · exact Tsubs hi
      apply Multiset.gcd_dvd; simp; exact hi
  -- Apply card_le_card to this and simplify
    apply card_le_card at this; rw [Tcard, Nat.Icc_succ_left, Nat.Ioc_filter_dvd_card_eq_div] at this
    rw [add_comm, Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul] at this
    nth_rw 1 [← Nat.div_add_mod n T.val.gcd, mul_comm] at this
  -- Prove that $T.val.gcd$ is less than $d$
    replace this : T.val.gcd < d := by rw [← mul_lt_mul_left (Nat.div_pos_iff.mpr gcdbd)]; omega
  -- Specialize lcd to $T.val.gcd$ to show that $d$ is less than or equal to $T.val.gcd$, which is a contradiction
    specialize lcd h (by intro l hl; apply Multiset.gcd_dvd; simp; exact hT hl)
    omega; exact dpr.pos
-- Now if we assume $k$ to be an integer with the desired properties in question, we need to show $k$ is greater or equal to $1+n/d$
-- We proceed by contradiction, we will construct a set that violates the assumption hk
  intro k Scardle hk; by_contra! h
-- Take a subset of all multiples of $d$ containing $S$ with cardinality $k$
  obtain ⟨T, ⟨hT, Tsubs, Tcard⟩⟩ := exists_subsuperset_card_eq Ssubs Scardle (by rw [Nat.Icc_succ_left, Nat.Ioc_filter_dvd_card_eq_div]; omega)
-- Prove that $d$ divides $T.val.gcd$
  have Tgcd : d ∣ T.val.gcd := by
    rw [Multiset.dvd_gcd]; intro x hx; rw [mem_val] at hx
    simp [subset_iff] at Tsubs; exact (Tsubs hx).right
-- Specialize hk to $T$ and derive a contradiction
  specialize hk T (by apply subset_trans Tsubs; apply filter_subset) hT Tcard
  simp [hk] at Tgcd; omega