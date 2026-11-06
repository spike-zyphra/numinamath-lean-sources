import Mathlib

open Finset

-- first prove a lemma that ∑ k ∈ Icc a b, 1 / ((k : ℚ) * (k + 1)) = 1 / a - 1 / (b + 1), forall a ≤ b, a ≥ 1
lemma sum_Icc : ∀ (a b : ℕ), a ≤ b → a ≥ 1 → ∑ k ∈ Icc a b, 
  1 / ((k : ℚ) * (k + 1)) = 1 / a - 1 / (b + 1):= by
  intro a b hab ha
  calc 
    _ = ∑ k ∈ Icc a b, (1 / (k : ℚ) - 1 / (k + 1 : ℚ)) := by 
      apply sum_congr rfl
      intro x hx
      simp at hx
      obtain ⟨hx1, hx2⟩ := hx
      have neq1 : (x : ℚ) ≠ 0 := by 
        norm_cast
        linarith
      have neq2 : (x + 1 : ℚ) ≠ 0 := by 
        norm_cast
      field_simp 
    _ = ∑ k ∈ Icc a b, 1 / (k : ℚ) - ∑ k ∈ Icc a b, 1 / (k + 1: ℚ):= by
      exact sum_sub_distrib
    _ = _ := by
      have aux1 : Icc a b = insert a (Icc (a + 1) b) := by 
        exact Eq.symm (Nat.Icc_insert_succ_left hab)
      have aux2 : Icc a b = insert b (Icc a (b-1)) := by
        refine Finset.ext_iff.mpr ?_
        intro x
        constructor
        · simp 
          intro hx1 hx2
          by_cases hb : x = b 
          · left
            exact hb
          · omega
        · simp
          intro hx1
          obtain hx1 | hx1 := hx1
          · simp [hx1]
            linarith
          · omega
      nth_rw 1 [aux1]
      rw [sum_insert, aux2, sum_insert]
      have aux3 : ∑ x ∈ Icc (a + 1) b, 1 / (x : ℚ) = ∑ x ∈ Icc a (b - 1), 1 / (x + 1: ℚ) := by 
        let t : ℕ → ℕ := fun n => n - 1
        let s : ℕ → ℕ := fun n => n + 1
        refine sum_nbij' t s ?_ ?_ ?_ ?_ ?_ 
        · simp
          intro x hx1 hx2
          unfold t
          constructor
          omega
          omega
        · simp
          intro x hx1 hx2
          unfold s
          constructor
          omega
          omega
        · simp
          intro x hx1 hx2
          unfold s t
          omega
        · simp 
          intro x hx1 hx2
          unfold s t 
          omega
        · simp 
          intro x hx1 hx2
          unfold t 
          have aux1 : ((x - 1 : ℕ) : ℚ) = (x : ℚ) - 1 := by
            rw [Nat.cast_sub]
            simp
            linarith
          linarith
      rw [aux3]
      ring
      simp
      intro hb
      linarith
      simp

theorem number_theory_635448 {X : ℕ} (hX : 1 ≤ X) (n : ℕ) (hn : X < n) :
  ∃ (i j : ℕ), i ≤ j ∧ (1 / (n - X + 1 : ℚ)) = ∑ k ∈ Finset.Icc i j, (1 / ((k : ℚ) * (k + 1))) ∧
  (i = n - X ∧ j = (n - X) * (n - X + 1) - 1) := by 
  use (n - X), (n - X) * (n - X + 1) - 1 
  have ineq : n - X ≤ (n - X) * (n - X + 1) - 1 := by 
    have ineq1 : n - X ≥ 1 := by 
      omega
    have ineq2 : n - X + 1 ≥ 2 := by 
      linarith
    calc 
      _ ≤ (n - X) * 2 - 1 := by 
        omega
      _ ≤ (n - X) * (n - X + 1) - 1 := by 
        have aux : (n - X) * 2 ≤ (n - X) * (n - X + 1) := by
          nlinarith
        omega
  constructor
  · exact ineq
  constructor
  · rw [sum_Icc _ _ ineq]
    have aux2 : (↑((n - X) * (n - X + 1) - 1 : ℕ) + (1 : ℚ)) = 
      (n - X) * (n - X + 1) := by 
      rw [Nat.cast_sub]
      norm_num
      rw [Nat.cast_sub]
      linarith
      omega
    rw [aux2, Nat.cast_sub]
    have neq1 : (↑n - ↑X + (1 : ℚ)) ≠ 0 := by 
      have pos : ↑n - ↑X + (1 : ℚ) > 0 := by 
        rw [←Nat.cast_sub]
        norm_cast
        linarith
        linarith
      linarith
    have neq2 : (n - (X : ℚ)) ≠ 0 := by 
      have pos : (n - (X : ℚ)) > 0 := by 
        rw [←Nat.cast_sub]
        norm_cast
        omega
        linarith
      linarith
    field_simp
    linarith
    omega
  exact ⟨rfl, rfl⟩