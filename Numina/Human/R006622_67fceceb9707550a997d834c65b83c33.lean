import Mathlib
set_option linter.unusedVariables false

/-Let $M$ be a natural number greater than 1. Determine the set of all natural numbers $n$ such that $1 \leq n < M$ and it is possible to obtain exactly $M$ pieces of paper by starting with $n$ pieces and repeatedly applying an operation where some chosen pieces of paper are each divided into exactly $n$ parts. Show that this set consists of precisely all natural numbers $n$ of the form $d+1$, where $d$ is a proper positive divisor of $M-1$. (A proper positive divisor $d$ of $X$ is a positive integer $d$ such that $d \mid X$ and $d < X$.)-/
theorem number_theory_639330 (M : ℕ) (hM : M > 1) :
  {n : ℕ | 1 ≤ n ∧ n < M ∧ ∃ (s : ℕ) (hs : s ≥ 1), ∃ (k : ℕ → ℕ), 
  (∀ j < s, k j ≥ 1) ∧ ∃ P : ℕ → ℕ, P 0 = n ∧ (∀ i < s, P (i + 1) = P i + k i * (n - 1)) ∧ (∀ j < s, k j ≤ P j) ∧ P s = M}
  = {n : ℕ | ∃ d : ℕ, d > 0 ∧ d ∣ (M - 1) ∧ d < (M - 1) ∧ n = d + 1} := by
  -- Define $SP$: Set of $n$ satisfying the problem's paper division conditions.
  let SP := {n : ℕ | 1 ≤ n ∧ n < M ∧ ∃ (s : ℕ) (hs : s ≥ 1), ∃ (k : ℕ → ℕ), 
    (∀ j < s, k j ≥ 1) ∧ ∃ P : ℕ → ℕ, P 0 = n ∧ (∀ i < s, P (i + 1) = P i + k i * (n - 1)) ∧ (∀ j < s, k j ≤ P j) ∧ P s = M}
  -- Define $SD$: Set of $n = d + 1$ where $d$ is a proper positive divisor of $M - 1$.
  let SD := {n : ℕ | ∃ d : ℕ, d > 0 ∧ d ∣ (M - 1) ∧ d < (M - 1) ∧ n = d + 1}
  -- Prove $SP ⊆ SD$: If $n$ in $SP$, then $n$ corresponds to a proper divisor $d$.
  have h_subset : SP ⊆ SD := by
    intro n hn
    rcases hn with ⟨hn1, hnM, s, hs, k, hk1, P, hP0, hP_rec, hP_le, hPs⟩
    let K := ∑ i ∈ Finset.range s, k i
    have hK_ge1 : K ≥ 1 := by
      apply Finset.sum_pos (fun i hi => Nat.lt_of_succ_le (hk1 i (Finset.mem_range.mp hi)))
      exact Finset.nonempty_range_iff.mpr (Nat.not_eq_zero_of_lt (Nat.lt_of_succ_le hs))
    have hP : ∀ i ≤ s, P i = n + (∑ j ∈ Finset.range i, k j) * (n - 1) := by
      intro i hi
      induction' i with i ih
      · simp [hP0]
      · rw [hP_rec i (Nat.lt_of_succ_le hi)]
        rw [ih (Nat.le_of_succ_le hi)]
        rw [Finset.sum_range_succ]
        ring
    -- Derive the key equation $M = n + K * (n - 1)$ from the recurrence.
    have hM_eq : M = n + K * (n - 1) := by 
      rw [← hPs]
      rw [hP s le_rfl]
    have hn_gt1 : n > 1 := by
      by_contra h_not
      have h_n1 : n = 1 := by linarith
      rw [h_n1] at hM_eq
      simp at hM_eq
      linarith
    let d := n - 1
    have hd_ge1 : d ≥ 1 := by omega
    -- Rewrite equation to $M - 1 = d * (K + 1)$ to establish divisibility.
    have hM_d : M - 1 = d * (K + 1) := by 
      unfold d
      rw [hM_eq]
      ring_nf
      omega
    have h_dvd : d ∣ (M - 1) := by
      rw [hM_d]
      exact dvd_mul_right d (K + 1)
    have hd_lt : d < M - 1 := by
      have hK_plus : K + 1 ≥ 2 := by linarith
      have h_div : d = (M - 1) / (K + 1) := by
        rw [hM_d]
        field_simp
      rw [h_div]
      nlinarith
    have hn_d : n = d + 1 := by simp [d];omega
    exact ⟨d, hd_ge1, h_dvd, hd_lt, hn_d⟩
  -- Prove $SD ⊆ SP$: If $n = d + 1$ for proper divisor $d$, then $n$ satisfies the conditions.
  have h_superset : SD ⊆ SP := by
    intro n hn
    rcases hn with ⟨d, hd_ge1, h_dvd, hd_lt, hn_d⟩
    have hn1 : 1 ≤ n := by linarith
    have hnM : n < M := by omega
    have hJ_ge2 : ∃ J ≥ 2, M - 1 = J * d := by
      let J := (M - 1) / d
      have hJ_dvd : M - 1 = J * d := by 
        unfold J
        exact (Nat.div_mul_cancel h_dvd).symm
      have hJ_ge2 : J ≥ 2 := by nlinarith
      exact ⟨J, hJ_ge2, hJ_dvd⟩
    rcases hJ_ge2 with ⟨J, hJ_ge2, hJ_dvd⟩
    let Ktot := J - 1
    have hKtot_ge1 : Ktot ≥ 1 := by omega
    let s := Ktot
    have hs_ge1 : s ≥ 1 := hKtot_ge1
    let k : ℕ → ℕ := fun _ => 1
    have hk1 : ∀ j < s, k j ≥ 1 := by intro j _; tauto
    let P : ℕ → ℕ := fun i => n + i * (n - 1)
    have hP0 : P 0 = n := by simp [P]
    have hP_rec : ∀ i < s, P (i + 1) = P i + k i * (n - 1) := by
      intro i _
      ring
    have hP_le : ∀ j < s, k j ≤ P j := by
      intro j hj
      simp [k, P]
      have hn_ge2 : n ≥ 2 := by linarith
      have hj_ge0 : j ≥ 0 := Nat.zero_le j
      nlinarith
    -- Verify that after $s$ operations, the final number of pieces $P s$ equals $M$.
    have hPs : P s = M := by
      simp [P]
      have hJ_dvd': M = J * d + 1 := by omega
      rw [hn_d, hJ_dvd']
      have h_s : s = J - 1 := rfl
      rw [h_s]
      norm_num
      rw [Nat.sub_mul, one_mul, ← Nat.add_sub_assoc (by nlinarith)]
      omega
    exact ⟨hn1, hnM, s, hs_ge1, k, hk1, P, hP0, hP_rec, hP_le, hPs⟩
  -- Conclude set equality based on mutual subset inclusions.
  exact Set.eq_of_subset_of_subset h_subset h_superset