import Mathlib

open Nat Finset

-- since I add a 0 to the sequence, then the result will have one more solution {0}. 
theorem number_theory_117758 (a : ℕ → ℤ)
    (h0 : a 0 = 0)
    (h1 : a 1 = 1)
    (h2 : a 2 = 3)
    (han : ∀ n, a (n + 2) = (n + 3) * a (n + 1) - (n + 2) * a n) :
    {n | 11 ∣ a n} = {0, 4, 8} ∪ {n | n ≥ 10} := by 
  -- We start by considering any integer $n$.
  -- we first prove the general formula for a_n 
  let b : ℕ → ℤ := fun n => a n - a (n - 1)
  have bneq : ∀ n, n ≥ 1 → b n = n.factorial := by 
    intro n
    induction n with 
    | zero => 
      simp_all
    | succ k ih => 
      by_cases hk : k = 0
      simp_all
      unfold b
      simp
      rw [h0, h1]
      norm_num
      have kge : k ≥ 1 := by 
        omega
      obtain keq1 := ih kge
      intro h'
      have aux : b (k + 1) = (k + 1) * b k := by 
        
        have eqaux : k + 1 = k - 1 + 2 := by 
          omega
        have aux2 : k - 1 + 1 = k := by
          omega
        have aux3 : k - 1 + 2 - 1 = k := by 
          omega
        conv => 
          unfold b
          lhs 
          rw [eqaux, han (k - 1), aux2, aux3]
        norm_cast
        have aux4 : k - 1 + 3 = k + 2 := by 
          omega
        have aux5 : (k - 1 + 2) = k +1 := by 
          omega
        rw [aux4, aux5]
        norm_num
        ring_nf
      rw [aux]
      obtain ih := ih kge
      rw [ih]
      conv =>
        rhs
        unfold factorial
        simp
  have aneq : ∀ n, a n = ∑ (k ∈ Finset.range n), (k + 1).factorial := by
    intro n
    induction n with 
    | zero =>
      simp
      rw [h0]
    | succ k ih => 
      have aux : a (k + 1) = b (k + 1) + a k := by 
        unfold b
        simp
      rw [aux, bneq, ih]
      norm_num
      -- Finset.sum_insert
      have ins_aux : insert k (range k) = range (k + 1) := by 
        exact Eq.symm range_add_one
      rw [←ins_aux]
      simp
      linarith
  have ha3 : a 3 = 9 := by
    rw [han]
    norm_cast
    rw [h1,h2]
    norm_num
  have ha4 : a 4 = 33 := by 
    rw [han, ha3, h2]
    norm_num
  have ha5 : a 5 = 153 := by
    rw [han, ha4, ha3]
    norm_num
  have ha6 : a 6 = 873 := by
    rw [han, ha5, ha4]
    norm_num
  have ha7 : a 7 = 5913 := by
    rw [han, ha6, ha5]
    norm_num
  have ha8 : a 8 = 46233 := by
    rw [han, ha7, ha6]
    norm_num
  have ha9 : a 9 = 409113 := by
    rw [han, ha8, ha7]
    norm_num
  have ha10 : a 10 = 4037913 := by
    rw [han, ha9, ha8]
    norm_num
  ext n
  constructor
  intro hn
  simp
  by_cases hnle : n < 10
  simp at hn
  interval_cases n
  rw [h0] at hn
  simp
  rw [h1] at hn
  norm_num at hn
  rw [h2] at hn
  norm_num at hn
  rw [ha3] at hn
  norm_num at hn
  simp
  rw [ha5] at hn
  norm_num at hn
  rw [ha6] at hn
  norm_num at hn
  rw [ha7] at hn
  norm_num at hn
  simp
  rw [ha9] at hn
  norm_num at hn
  simp at hnle
  right
  exact hnle
  intro hn
  simp at hn
  obtain hn | hn := hn
  obtain hn | hn | hn := hn
  simp 
  rw [hn, h0]
  norm_num
  simp [hn, ha4]
  norm_num
  simp [hn, ha8]
  norm_num
  simp
  -- Finset.dvd_sum
  rw [aneq]
  -- Finset.sum_disjUnion
  have aux1 : Disjoint  (range 10) (range n \ (range 10)) := by 
    exact disjoint_sdiff
  have aux2 : (range 10).disjUnion (range n \ (range 10)) aux1 = range n := by
    simp [hn]
  rw [←aux2, sum_disjUnion]
  norm_cast
  have dvd1 : 11 ∣ ∑ x ∈ range 10, (x + 1)! := by 
    have aux : (11 : ℤ) ∣ (∑ x ∈ range 10, (x + 1)! : ℕ) := by 
      rw [←aneq (10)]
      rw [ha10]
      norm_num
    norm_cast
  have dvd2 : 11 ∣ ∑ x ∈ (range n \ range 10), (x + 1)! := by 
    apply dvd_sum
    intro i hi
    simp at hi
    obtain ⟨hi1, hi2⟩ := hi
    apply Nat.dvd_factorial
    positivity
    linarith
  exact (Nat.dvd_add_iff_right dvd1).mp dvd2

  