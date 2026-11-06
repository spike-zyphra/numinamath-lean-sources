import Mathlib

open Finset

/-How many integers $n$ are there subject to the constraint that $1 \leq n \leq 2020$ and $n^n$ is a perfect square? -/
theorem number_theory_88149 : #{a ∈ image (fun n => n ^ n) (Icc 1 2020) | IsSquare a} = 1032 := by
-- Denote the set in question by $s$
  set s := {a ∈ image (fun n => n ^ n) (Icc 1 2020) | IsSquare a}
-- Partition $s$ into a subset $s1$ of odd numbers and a subset $s2$ of even numbers
  let s1 := {a ∈ s | Even a}; let s2 := {a ∈ s | Odd a}
  have disj : Disjoint s1 s2 := by
    simp [disjoint_iff, Finset.ext_iff, s1, s2]
    intros; assumption
  have hu : s = s1 ∪ s2 := by
    simp [Finset.ext_iff, s1, s2]; intro n
    rw [← and_or_left, iff_self_and]; intro
    apply Nat.even_or_odd
  rw [hu, card_union_of_disjoint disj]
-- Denote the function sending $i$ to $(2 * i) ^ (2 * i)$ by $f1$ and prove it is strictly increasing
  let f1 : ℕ → ℕ := fun i => (2 * i) ^ (2 * i)
  have f1mono : StrictMono f1 := by
    apply strictMono_of_lt_succ; simp
    intro i; dsimp [f1]; by_cases h : i = 0
    · simp [h]
    calc
      _ < (2 * (i + 1)) ^ (2 * i) := by gcongr; simp
      _ < _ := by gcongr; omega; simp
-- Prove that $s1$ is the image of $[1,1010]$ under $f1$
  have f1img : image f1 (Icc 1 1010) = s1 := by
    simp [Finset.ext_iff, f1, s1, s, and_assoc]
    intro x; constructor
    · rintro ⟨n, nge, nle, hn⟩; split_ands
      · use 2 * n; omega
      · use (2 * n) ^ n; rw [← hn]; ring
      rw [← hn, Nat.even_pow]; simp; omega
    rintro ⟨⟨m, mge, mle, hm⟩, _, xpar⟩
    rw [← hm, Nat.even_pow] at xpar; rcases xpar with ⟨⟨k, hk⟩⟩
    use k; split_ands; any_goals omega
    rw [← hm, hk]; ring
-- This computes the cardinality of $s1$
  rw [← f1img, card_image_of_injective _ f1mono.injective]
-- Denote $f2$ to be the function sending $i$ to $((2 * i + 1) ^ 2) ^ ((2 * i + 1) ^ 2)$ and prove it is strictly increasing
  let f2 : ℕ → ℕ := fun i => ((2 * i + 1) ^ 2) ^ ((2 * i + 1) ^ 2)
  have f2mono : StrictMono f2 := by
    apply strictMono_of_lt_succ; simp
    intro i; dsimp [f2]; calc
      _ < ((2 * (i + 1) + 1) ^ 2) ^ (2 * i + 1) ^ 2 := by gcongr; simp
      _ < _ := by
        gcongr; zify; rw [← sub_pos]
        ring_nf; positivity; simp
-- Prove that $s2$ is the image of $[1,22]$ under $f1$
  have f2img : image f2 (range 22) = s2 := by
    simp [Finset.ext_iff, f2, s2, s, and_assoc]
    intro x; constructor
    · rintro ⟨n, nlt, hx⟩; split_ands
      · use (2 * n + 1) ^ 2; split_ands
        · zify; rw [← sub_nonneg]; ring_nf; positivity
        · calc
            _ ≤ ((2 * 21 + 1) ^ 2) := by gcongr; omega
            _ ≤ _ := by norm_num
        exact hx
      · use (2 * n + 1) ^ (2 * n + 1) ^ 2
        rw [← hx, pow_right_comm]; ring
      rw [← hx]; repeat apply Odd.pow
      use n
  -- For the reverse side, we need to show that if an odd number's odd power is a perfect square, then the number has to be a perfect square
    rintro ⟨⟨m, mge, mle, hm⟩, ⟨r, hr⟩, xpar⟩
    rw [← hm, Nat.odd_iff, Nat.pow_mod] at xpar
    by_cases h : m % 2 = 0
    · rw [h, zero_pow] at xpar
      all_goals omega
    clear xpar; replace h : m % 2 = 1 := by omega
    suffices : IsSquare m
    · rcases this with ⟨t, ht⟩
      rw [ht, Nat.mul_mod] at h
      replace h : t % 2 = 1 := by
        by_contra!; replace this : t % 2 = 0 := by omega
        norm_num [this] at h
      use t / 2; constructor
      · norm_num [Nat.div_lt_iff_lt_mul]; by_contra!
        replace this : 45 ≤ t := by omega
        rw [ht] at mle; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at this
        norm_num [pow_two] at this; omega
        all_goals simp
      rw [← h, Nat.div_add_mod, pow_two, ← ht]; exact hm
    rw [← pow_two] at hr; rw [hr] at hm; clear * - mge hm h
    have rne : r ≠ 0 := by intro h; simp [h] at hm
    use ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
    rw [← pow_two, ← prod_pow]
    nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show m≠0 by omega)]
    simp [Finsupp.prod]; apply prod_congr rfl
    intro p pmem; rw [← pow_mul, Nat.div_mul_cancel]
    replace h : Nat.Coprime 2 m := by
      simp; exact Nat.odd_iff.mpr h
    rw [← Nat.Coprime.dvd_mul_left h]
    let hp := pmem; simp at hp
    have : Fact (p.Prime) := ⟨hp.left⟩
    apply_fun fun t => padicValNat p t at hm
    rw [padicValNat.pow, padicValNat.pow] at hm
    use padicValNat p r; rw [Nat.factorization_def, hm]
    exact hp.left; any_goals exact rne
    omega
-- This computes the cardinality of $s2$ and finishes the goal
  rw [← f2img, card_image_of_injective _ f2mono.injective]
  norm_num