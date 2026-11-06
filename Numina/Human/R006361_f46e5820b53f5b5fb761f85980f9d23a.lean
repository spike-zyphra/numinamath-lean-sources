import Mathlib

open Finset

lemma sum_add_nine (n : ℕ) : (∑ x ∈ Icc n (n + 9), x) % 10 = 5 := by 
  induction n with 
  | zero => 
    simp
    rfl
  | succ k ih => 
    have aux1 : Icc (k + 1) (k + 1 + 9) = insert (k + 10) (Icc (k + 1) (k + 9)) := by
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    have aux2 : Icc k (k + 9) = insert k (Icc (k + 1) (k + 9)) := by 
      refine Eq.symm (Nat.Icc_insert_succ_left ?_)
      linarith
    rw [aux1, sum_insert, Nat.add_mod]
    rw [aux2, sum_insert, Nat.add_mod] at ih
    have aux3 : (k + 10) % 10 = k % 10 := by 
      apply Nat.modEq_of_dvd 
      omega
    rw [aux3]
    exact ih
    simp
    simp

lemma mod_eq_aux (i : ℕ) (m : ℕ) : i ^ (4 * m + 1) % 10 = i % 10 := by 
  induction m with 
  | zero => 
    simp
  | succ k ih => 
    have aux : 4 * (k + 1) + 1 = (4 * k + 1) + 4 := by 
      omega
    have aux2 : i * i ^ 4 = i ^ 5 := by 
      ring
    rw [aux, pow_add, Nat.mul_mod, ih, ← Nat.mul_mod, aux2, Nat.pow_mod]
    have i_mod_ten_le_ten : i % 10 < 10 := Nat.mod_lt _ (show 10 > 0 by norm_num)
    interval_cases i % 10 <;> simp_all

theorem number_theory_636257 (m : ℕ) (S : ℕ → ℕ) (hS : ∀ m, S m = ∑ i ∈ Icc 0 (10 * m + 4), (i + 2) ^ (4 * i + 1)) :
    if Even m then S m % 10 = 0 else S m % 10 = 5 := by 
  have h0 : (∑ x ∈ Icc 0 (10 * m + 4), x + ∑ x ∈ Icc 0 (10 * m + 4), 2) % 10 = 45 * m % 10 := by 
    induction m with 
    | zero => 
      simp
      rfl
    | succ k ih => 
      have aux3 : Disjoint (Icc 0 (10 * k + 4)) (Icc (10 * k + 5) (10 * (k + 1) + 4)) := by 
        refine (Finset.disjoint_iff_ne).mpr ?_ 
        intro x hx y hy
        simp at hx hy
        obtain ⟨hy1, hy2⟩ := hy
        linarith
      have aux2 : Icc 0 (10 * (k + 1) + 4) = 
        (Icc 0 (10 * k + 4)).disjUnion (Icc (10 * k + 5) (10 * (k + 1) + 4)) aux3 := by 
        ext x
        constructor
        · intro h
          simp
          by_cases hx1 : x ≤ 10 * k + 4
          · left
            linarith
          · right
            simp at hx1 h
            constructor
            · linarith
            · linarith
        · intro h
          simp at h
          obtain h | h := h
          · simp
            linarith
          · simp 
            linarith
      rw [aux2, sum_disjUnion, sum_disjUnion]
      have aux4 : ∑ x ∈ Icc 0 (10 * k + 4), x + ∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), x +
      (∑ x ∈ Icc 0 (10 * k + 4), 2 + ∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), 2)
        = (∑ x ∈ Icc 0 (10 * k + 4), x + ∑ x ∈ Icc 0 (10 * k + 4), 2)  + 
      (∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), x + ∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), 2) := by 
        ring
      rw [aux4, Nat.add_mod, ih]
      have aux5 : (∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), x + ∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), 2) % 10 = 5 := by 
        rw [Nat.add_mod]
        have aux6 : (∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), 2) % 10 = 0 := by 
          have mod1 : ∑ x ∈ Icc (10 * k + 5) (10 * (k + 1) + 4), 2 = 10 * 2 := by 
            simp
            omega
          rw [mod1]
        rw [aux6]
        simp
        have eq1 : (10 * (k + 1) + 4) = 10 * k + 5 + 9 := by 
          omega
        rw [eq1, sum_add_nine]
      rw [aux5]
      omega
  have h1 : S m % 10 = (45 * m ) % 10 := by 
    have aux1 : (∑ i ∈ Icc 0 (10 * m + 4), (i + 2) ^ (4 * i + 1) % 10)  = 
      (∑ i ∈ Icc 0 (10 * m + 4), (i + 2) % 10) := by 
      apply sum_congr rfl
      intro i hi
      exact mod_eq_aux (i + 2) i
    rw [hS, sum_nat_mod, aux1, ←sum_nat_mod, sum_add_distrib, h0]
  by_cases heven : Even m
  · -- the case m is Even
    rw [if_pos heven, h1]
    unfold Even at heven
    obtain ⟨r, hr⟩ := heven
    rw [hr]
    omega
  · -- the case m is Odd
    rw [if_neg heven]
    have odd_m : Odd m := by 
      exact Nat.not_even_iff_odd.mp heven
    obtain ⟨r, hr⟩ := odd_m
    rw [h1, hr]
    omega