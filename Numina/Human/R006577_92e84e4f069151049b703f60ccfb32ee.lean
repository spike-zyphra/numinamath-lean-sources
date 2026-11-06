import Mathlib

open Finset

lemma sum_sq (n : ℕ) : 6 * ∑ i ∈ range n, i ^ 2 =  (n * (n - 1) * (2*n - 1)) := by
    induction n with
    | zero => simp
    | succ m ih => 
      have aux : range (m + 1) = insert m (range m) := by 
        exact range_add_one
      rw [aux, sum_insert, mul_add, ih]
      by_cases hm0 : m = 0 
      · rw [hm0]
        simp
      · have mge : m ≥ 1 := by 
          omega
        zify
        have cast1 : (m - 1 : ℕ) = (m : ℤ) - 1 := by 
          have ge1 : m ≥ 1 := by 
            linarith
          omega
        have cast2 : (2 * m - 1 : ℕ) = (2 * m : ℤ) - 1 := by 
          have ge2 : 2 * m ≥ 1 := by
            linarith
          omega
        have cast3 : ↑(m + 1 - 1 : ℕ) = ((m : ℤ) + 1 - 1) := by 
          have ge1 : m + 1 ≥  1 := by 
            omega
          omega
        have cast4 : ↑(2 * (m + 1) - 1 : ℕ) = (2 * ((m : ℤ) + 1) - 1) := by 
          have ge1 : 2 * (m + 1) ≥  1 := by 
            omega
          omega
        rw [cast1, cast2, cast3, cast4]
        ring_nf
      simp

lemma sum_id (n : ℕ): 2 * ∑ i ∈ range n, i = n * (n - 1) := by 
  induction n with
    | zero => simp
    | succ m ih => 
      have aux : range (m + 1) = insert m (range m) := by 
        exact range_add_one
      rw [aux, sum_insert, mul_add, ih]
      by_cases hm0 : m = 0 
      · rw [hm0]
      · have mge : m ≥ 1 := by 
          omega
        zify
        have cast1 : (m - 1 : ℕ) = (m : ℤ) - 1 := by 
          have ge1 : m ≥ 1 := by 
            linarith
          omega
        have cast2 : (m + 1 - 1 : ℕ) = ((m : ℤ) + 1 - 1) := by
          have ge1 : m + 1 ≥  1 := by
            omega
          omega
        rw [cast1, cast2]
        ring
      simp
  

theorem number_theory_638665 {N : ℕ} (hN : N = 33818) (k : ℕ) (hk : k > 0) :
    (∑ i ∈ range k, (N + i)^2) % 17 = ((k % 17) * (2 * (k % 17) + 3) * (3 * (k % 17) + 2)) % 17 := by 
  have eq1 : (∑ i ∈ range k, (N + i)^2) % 17 = (∑ i ∈ range k, (5 + i)^2) % 17 := by 
    conv =>
      lhs 
      rw [sum_nat_mod] 
    conv =>   
      rhs
      rw [sum_nat_mod]
    have aux : (∑ i ∈ range k, (N + i) ^ 2 % 17) = (∑ i ∈ range k, (5 + i) ^ 2 % 17) := by
      apply sum_congr rfl
      intro x hx
      rw [hN]
      ring_nf
      omega
    rw [aux]
  rw [eq1]
  
  have cast1 : (k - 1 : ℕ) = (k : ℤ) - 1 := by 
    have ge1 : k ≥ 1 := by 
      linarith
    omega
  have cast2 : (2 * k - 1 : ℕ) = (2 * k : ℤ) - 1 := by 
    have ge2 : 2 * k ≥ 1 := by
      linarith
    omega
  
  have eq3 : (6 * ∑ i ∈ range k, (5 + i) ^ 2) % 17 = 
    (48 * k + 30 * k * (k - 1) + k * (k - 1) * (2 * k - 1)) % 17 := by 
    calc 
      _ = (6 * ∑ i ∈ range k, (25 + 10 * i + i ^ 2)) % 17  := by 
        have aux1 : ∑ i ∈ range k, (5 + i) ^ 2 = ∑ i ∈ range k, (25 + 10 * i + i ^ 2) := by
          apply sum_congr rfl
          intro x hx
          ring
        rw [aux1]
      _ = _ := by   
        have aux1 : (6 * ∑ i ∈ range k, (25 + 10 * i + i ^ 2)) = 
          (150 * k + 30 * k * (k - 1) + k * (k - 1) * (2 * k - 1)) := by 
          rw [sum_add_distrib, sum_add_distrib, ←mul_sum, mul_add, mul_add]
          rw [sum_sq]
          have aux2 : 10 * ∑ i ∈ range k, i = 5 * (2 * ∑ i ∈ range k, i) := by 
            ring
          rw [aux2, sum_id]
          simp
          ring_nf
        rw [aux1]
        apply Nat.modEq_of_dvd
        norm_num
        omega
  have eq4 : (∑ i ∈ range k, (5 + i) ^ 2) % 17 = 
    (8 * k + 90 * k * (k - 1) + 3 * k * (k - 1) * (2 * k - 1)) % 17 := by 
    have aux : ((6 * ∑ i ∈ range k, (5 + i) ^ 2 )* 3) % 17 = ((48 * k + 30 * k * (k - 1) + k * (k - 1) * (2 * k - 1)) * 3) % 17 := by 
      apply Nat.modEq_of_dvd
      obtain aux3 := Nat.ModEq.dvd eq3
      have aux2 : (((48 * k + 30 * k * (k - 1) + k * (k - 1) * (2 * k - 1)) * 3 : ℕ) : ℤ) - ↑((6 * ∑ i ∈ range k, (5 + i) ^ 2) * 3 : ℕ) =
      ((((48 * k + 30 * k * (k - 1) + k * (k - 1) * (2 * k - 1)) : ℕ) : ℤ)- (((6 * ∑ i ∈ range k, (5 + i) ^ 2): ℕ) : ℤ)) * 3:= by 
        norm_num 
        ring
      rw [aux2]
      obtain ⟨y, hy⟩ := aux3
      use y*3
      rw [hy]
      ring
    have aux2 : ((6 * ∑ i ∈ range k, (5 + i) ^ 2 )* 3) % 17 = 
      (( ∑ i ∈ range k, (5 + i) ^ 2 )) % 17 := by 
      apply Nat.modEq_of_dvd
      omega
    rw [aux2] at aux
    rw [aux]
    apply Nat.modEq_of_dvd
    norm_num
    rw [cast1, cast2]
    ring_nf
    omega
  have eq5 : (8 * k + 90 * k * (k - 1) + 3 * k * (k - 1) * (2 * k - 1)) % 17 
    = (8 * k + 5 * k * (k - 1) + 3 * k * (k - 1) * (2 * k - 1)) % 17:= by 
    apply Nat.modEq_of_dvd
    norm_num
    rw [cast1]
    ring_nf
    omega
  rw [eq4, eq5]
  have eq6 : (8 * k + 5 * k * (k - 1) + 3 * k * (k - 1) * (2 * k - 1)) % 17 = 
    (6 * k ^ 3 + 13 * k ^ 2 + 6 * k) % 17 := by 
    apply Nat.modEq_of_dvd
    norm_num
    rw [cast1, cast2]
    ring_nf
    simp
  have eq_aux : 6 * k ^ 3 + 13 * k ^ 2 + 6 * k = k * (2 * k + 3) * (3 * k + 2) := by 
    ring
  rw [eq6, eq_aux]
  calc 
    _ = (k * (2 * k + 3) % 17) * ((3 * k + 2 )% 17) % 17 := by 
      rw [Nat.mul_mod, Nat.mul_mod]
    _ = ((k % 17) * ((2 * k + 3 ) % 17) % 17) * ((3 * k + 2 )% 17) % 17 := by 
      simp
    _ = _ := by 
      have aux : k % 17 * ((2 * k + 3) % 17) % 17 = k % 17 * (2 * (k % 17) + 3) % 17 := by 
        rw [Nat.mul_mod]
        nth_rw 2 [Nat.mod_mod]
        have aux3 : ((2 * k + 3) % 17) =  (2 * (k % 17) + 3)%17:= by
          omega
        rw [aux3]
        simp
      have aux2 : ((3 * k + 2) % 17) = (3 * (k % 17) + 2)%17 := by 
        omega
      rw [aux, aux2]
      rw [←Nat.mul_mod]