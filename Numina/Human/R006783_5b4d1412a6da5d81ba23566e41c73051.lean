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

lemma sum_range_sq (n : ℕ) : ∑ i ∈ range n, i ^ 2 =  (n * (n - 1) * (2*n - 1)) / 6 := by 
  rw [←sum_sq n]
  simp


theorem number_theory_641120 (k : ℕ) (s : ℤ) (a : ℕ → ℕ) (kpos : k > 0)
  (hpos : ∀ i ∈ range k, 0 < a i)
  (hmod : ∀ j ∈ range k, a j % 100 = (s + j) % 100) :
  (∑ i ∈ range k, a i ^ 2) % 100 = (k * s ^ 2 + s * k * (k - 1) + k * (k - 1) * (2 * k - 1) / 6) % 100 := by 
  have h1 : (∑ i ∈ range k, a i ^ 2) % (100 : ℤ) = 
    (∑ i ∈ range k, ((s + i) % 100) ^ 2) % 100 := by 
    have aux : (∑ i ∈ range k, a i ^ 2 % (100 : ℤ)) = (∑ i ∈ range k, ((s + i) % 100) ^ 2 % (100 : ℤ)) := by 
      apply sum_congr rfl
      intro i hi
      rw [←hmod i hi]
      norm_cast
      exact Nat.pow_mod (a i) 2 100
    norm_num
    rw [sum_int_mod, aux]
    conv => 
      rhs
      rw [sum_int_mod]
  rw [h1]
  have h2 : (∑ i ∈ range k, ((s + ↑i) % 100) ^ 2) % (100 : ℤ) = 
    (∑ i ∈ range k, (s + ↑i)^ 2) % 100 := by 
    rw [sum_int_mod]
    conv => 
      rhs
      rw [sum_int_mod]
    have eq1 : (∑ i ∈ range k, ((s + ↑i) % 100) ^ 2 % 100) = 
      (∑ i ∈ range k, (s + ↑i) ^ 2 % 100) := by 
      apply sum_congr rfl
      intro i hi
      refine Int.ModEq.eq ?_
      have aux : ((s + ↑i) % 100) ≡ s + ↑i [ZMOD 100] := by 
        apply Int.modEq_of_dvd 
        omega
      exact Int.ModEq.pow 2 aux
    rw [eq1]
  have h3 : (∑ i ∈ range k, (s + ↑i)^ 2) = 
    (↑k * s ^ 2 + s * ↑k * (↑k - 1) + ↑k * (↑k - 1) * (2 * ↑k - 1) / 6) := by 
    calc 
      _ = ∑ i ∈ range k, (s^2 + 2 * s * ↑i + (↑i)^2) := by
        apply sum_congr rfl
        intro i hi
        ring
      _ = ∑ i ∈ range k, s ^ 2 + 2 * s *  ∑ i ∈ range k, i + ∑ i ∈ range k, i ^ 2 := by 
        rw [sum_add_distrib, sum_add_distrib]
        congr 
        rw [←mul_sum]
        norm_num
        norm_num
      _ = _ := by 
        have aux1 : ∑ i ∈ range k, s ^ 2 = k * s ^ 2 := by 
          simp
        have aux2 : 2 * s *  ∑ i ∈ range k, i  = s * ↑k * (↑k - 1) := by
          rw [sum_range_id]
          norm_num
          rw [Nat.cast_sub]
          norm_num
          have dvd1 : (2 : ℤ) ∣ k * (k - 1) := by 
            -- discuss by cases that k is odd or even
            by_cases oddk : Odd k
            -- the cases k is Odd
            · have aux : Even ((k : ℤ) - 1) := by
                obtain ⟨t, ht⟩ := oddk
                use t
                rw [ht]
                norm_num
                ring
              have dvd2 : 2 ∣ (k : ℤ) - 1 := by 
                exact even_iff_two_dvd.mp aux
              exact Dvd.dvd.mul_left dvd2 (k : ℤ)
            -- the case k is Even
            simp at oddk
            have dvd2 : 2 ∣ (k : ℤ) := by 
              obtain ⟨t, ht⟩ := oddk
              use t
              rw [ht]
              norm_num
              ring_nf
            exact Dvd.dvd.mul_right dvd2 (↑k - 1)
          obtain ⟨t, ht⟩ := dvd1
          rw [ht]
          conv => 
            rhs
            rw [mul_assoc, ht]
          simp 
          ring
          omega
        have aux3 : ∑ i ∈ range k, i ^ 2 = k * (k - 1) * (2 * k - 1) / 6 := by 
          exact sum_range_sq k
        rw [aux1, aux2, aux3]
        norm_num
        rw [Nat.cast_sub, Nat.cast_sub]
        norm_num
        omega
        omega
  rw [h2, h3]