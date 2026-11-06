import Mathlib

open Finset Real Nat

/-How many 2-digit positive integers have an even number of positive divisors?-/

theorem number_theory_611117: {n: ℕ | (10 ≤ n) ∧ (n ≤ 99) ∧ Even (Nat.divisors n).card }.encard = 84 := by
  let A:= {n: ℕ | (10 ≤ n) ∧ (n ≤ 99) ∧ Even (Nat.divisors n).card }
  let B:= {n: ℕ | (10 ≤ n) ∧ (n ≤ 99) ∧ Odd (Nat.divisors n).card }

  have find_B: B = {16,25,36,49,64,81} := by
    simp [B]
    ext n
    constructor

    . intro hn
      simp at hn
      rcases hn with ⟨bn1,bn2,hn⟩
      by_contra! no
      simp at no
      absurd hn
      simp
      have ln: n ∈ Icc 10 15 ∨ n ∈ Icc 17 24 ∨ n ∈ Icc 26 35 ∨ n ∈ Icc 37 48 ∨ n ∈ Icc 50 63 ∨ n ∈ Icc 65 80 ∨ n ∈ Icc 82 99 := by
        simp
        omega
      rcases ln with ln | ln | ln | ln | ln | ln | ln
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide
      . fin_cases ln
        all_goals native_decide

    . intro hn
      simp at hn
      simp
      rcases hn with hn | hn | hn | hn | hn | hn
      . simp [hn]
        decide
      . simp [hn]
        decide
      . simp [hn]
        decide
      . simp [hn]
        decide
      . simp [hn]
        decide
      . simp [hn]
        decide

  have B_card: B.encard = 6 := by
    rw [find_B]
    simp [Set.encard]

  have h_union: A ∪ B = Icc 10 99 := by
    ext x
    constructor
    · intro hx
      simp [A,B] at hx
      simp
      omega
    . intro hx
      simp [A,B]
      simp at hx
      simp [hx]
      exact Nat.even_or_odd ((divisors x).card)

  have h_disjoint: Disjoint A B := by
    simp [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp
    intro hx
    by_contra! hy
    simp [A,B] at hx hy
    rcases hx with ⟨hx1, hx2, hx3⟩
    rcases hy with ⟨hy1, hy2, hy3⟩
    absurd hy3
    simp
    exact hx3

  have card_sum: A.encard + B.encard = (A ∪ B).encard := by
    symm
    apply Set.encard_union_eq h_disjoint

  simp [h_union] at card_sum

  have count_card: (Set.Icc 10 99).encard = 90 := by
     rw [show Set.Icc 10 99 = ↑(Icc 10 99) by simp]
     rw [Set.encard_coe_eq_coe_finsetCard]
     simp

  have A_card: A.encard = 84 := by
    rw [count_card] at card_sum
    rw [B_card] at card_sum
    set a:= A.encard with ha
    clear_value a
    clear *- card_sum
    have ne: a ≠ ⊤ := by
      by_contra! no
      simp [no] at card_sum
    set b:= a.toNat with hb
    have hb2: a = ↑b := by
      symm at hb
      rw [ENat.toNat_eq_iff] at hb
      exact hb
      by_contra! no
      simp [no] at hb
      simp [ne] at hb
      simp [hb] at card_sum
    simp [hb2]
    norm_cast
    simp [hb2] at card_sum
    norm_cast at card_sum
    omega

-- Finally, substituting back to the original statement --
  simp [A,A_card]