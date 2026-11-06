import Mathlib

open Finset

/-Est-il possible de trouver un bloc de 1000 nombres entiers strictement positifs consécutifs qui contient exactement 5 nombres premiers?-/
theorem number_theory_607238 : ∃ n : ℕ, {p ∈ Icc n (n + 999) | p.Prime}.card = 5 := by
-- Denote $p$ to be the cardinality of the set in question
  let P : ℕ → ℕ := fun n => {p ∈ Icc n (n + 999) | p.Prime}.card
-- Prove that $5< p(0)$ and $5< p(1)$ by exhibiting $6$ prime numbers between $1$ and $1000$
  have P1 : 5 < P 0 ∧ 5 < P 1 := by
    constructor
    · dsimp [P]; suffices : {2, 3, 5, 7, 11, 13} ⊆ {p ∈ Icc 0 999| p.Prime}
      · apply card_le_card at this; apply lt_of_lt_of_le _ this; simp
      simp [subset_iff]; split_ands; all_goals norm_num
    dsimp [P]; suffices : {2, 3, 5, 7, 11, 13} ⊆ {p ∈ Icc 1 1000| p.Prime}
    · apply card_le_card at this; apply lt_of_lt_of_le _ this; simp
    simp [subset_iff]; split_ands; all_goals norm_num
-- Prove that $P(1001!+2)$ is $0$ since all the numbers from $1001!+2$ to $1001!+1001$ are composite
  have Peq0 : P (Nat.factorial 1001 + 2) = 0 := by
    dsimp [P]; rw [card_filter_eq_zero_iff]; intro x hx; simp at hx
    simp [Nat.prime_def]; intro; use x - Nat.factorial 1001; split_ands
    · nth_rw 2 [show x = x - Nat.factorial 1001 + Nat.factorial 1001 by omega]
      rw [← Nat.dvd_add_iff_right]; apply Nat.dvd_factorial; any_goals omega
      rfl
    omega; suffices : x - Nat.factorial 1001 < x; omega
    apply Nat.sub_lt; omega; positivity
-- As a corollary from Peq0, we get the following existence proposition
  have EXk : ∃ k, P k ≤ 5 := by use Nat.factorial 1001 + 2; simp [Peq0]
-- Fulfill the final goal with Nat.find EX and prove it satisfies the desired property
  use Nat.find EXk; have kspec := Nat.find_spec EXk
  have lekiff := Nat.le_find_iff EXk; push_neg at lekiff; set k := Nat.find EXk
-- Prove that $k$ is larger than $1$
  have kgt : 1 < k := by by_contra!; interval_cases k; all_goals omega
-- Prove that $P(k-1)$ is larger than $5$
  have Pks1 : 5 < P (k - 1) := by
    specialize lekiff k; simp at lekiff; apply lekiff
    apply Nat.sub_lt; omega; simp
-- Prove that $P k = 5$ and the goal follows
  have Pk : P k = 5 := by
    rw [Nat.eq_iff_le_and_ge]; constructor; exact kspec
    dsimp [P]; dsimp [P] at Pks1; rw [← Nat.Icc_insert_succ_right, filter_insert]
    rw [← Nat.Icc_insert_succ_left, filter_insert, Nat.sub_add_cancel] at Pks1;
    rw [show k-1+999 = k+998 by omega] at Pks1; rw [show k+998+1 = k+999 by ring] at *; split_ifs at *
    · rw [card_insert_of_not_mem] at *; any_goals omega
      · simp; intros; omega
      simp
    · rw [card_insert_of_not_mem] at *; any_goals omega
      simp
    · rw [card_insert_of_not_mem] at *; any_goals omega
      simp; intros; omega
    all_goals omega
  dsimp [P] at Pk; exact Pk