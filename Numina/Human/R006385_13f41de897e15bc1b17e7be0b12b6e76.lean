import Mathlib

open Nat


lemma nat_le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega



lemma nat_div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [nat_le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega


lemma nat_div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, nat_div_le_iff_le_mul h]

theorem number_theory_636509 (x : ℕ) (hx : 1 < x) :
    Nat.lcm (x ^ 4 - 1) (x ^ 5 + 1) = (x - 1) * (x ^ 2 + 1) * (x ^ 5 + 1) := by
  have hx4 : x ^ 4 > 1 := by
    have h1 : x ^ 4 > 1 := by
      apply Nat.one_lt_pow
      norm_num
      exact hx
    exact h1
  have hx5 : x ^ 5 > 0 := by
    apply Nat.pos_pow_of_pos
    linarith
  have h1 : x ^ 4 - 1 > 0 := by
    omega
  have h2 : x ^ 5 + 1 > 0 := by
    omega
  have h3 : Nat.gcd (x ^ 4 - 1) (x ^ 5 + 1) = x + 1 := by
    have h4 : x ^ 5 + 1 = (x ^ 4 - 1) * x + (x + 1) := by
      ring_nf
      have aux : x * (x ^ 4 - 1) = x * x ^ 4 - x := by 
        exact Nat.mul_sub_one x (x ^ 4)
      rw [aux]
      have aux1 : x * x ^ 4 - x = x ^ 5 - x := by 
        ring_nf
      rw [aux1]
      zify
      have aux2 : ↑(x ^ 5 - x : ℕ) = (x : ℤ) ^ 5 - x := by 
        have pos : x ^ 5 ≥  x := by 
          calc 
            _ = x * x ^ 4 := by 
              ring
            _ ≥ x * 1 := by 
              refine Nat.mul_le_mul_left x ?_
              linarith
            _ = x := by simp
        norm_cast
      rw [aux2]
      ring
    have h5 : Nat.gcd (x ^ 4 - 1) (x ^ 5 + 1) = Nat.gcd (x ^ 4 - 1) (x + 1) := by
      rw [h4]
      simp [Nat.gcd_add_mul_self]
    have h6 : Nat.gcd (x ^ 4 - 1) (x + 1) = x + 1 := by
      have h7 : x ^ 4 - 1 = (x + 1) * (x ^ 3 - x ^ 2 + x - 1) := by
        ring_nf
        zify
        have aux1 : ↑(x ^ 4 - 1 : ℕ) = (x : ℤ) ^ 4 - 1:= by 
          have pos :  x ^ 4 ≥ 1 := by 
            linarith
          norm_cast
        rw [aux1]
        have aux2 : ↑(x + (x ^ 3 - x ^ 2) - 1 : ℕ) = ((x : ℤ) + ((x : ℤ) ^ 3 - (x : ℤ) ^ 2) - 1)
          := by 
          have pos1 : x ^ 3 ≥ x ^ 2 := by 
            calc 
              _ = x ^ 2 * x := by   
                ring
              _ ≥ x^ 2 * 1 := by 
                refine Nat.mul_le_mul_left (x ^ 2) ?_
                linarith
              _ = _ := by 
                simp
          have pos2 : x ≥ 1 := by 
            linarith
          calc 
            _ = (((x ^ 3 - x ^ 2) + x - 1 : ℕ ) : ℤ) := by 
              rw [add_comm]
            _ = (x ^ 3 - x ^ 2 : ℕ) + (x - 1 : ℕ) := by 
              norm_cast
              omega
            _ = (x ^ 3 - x ^ 2 ) + (x - 1) := by 
              norm_cast
            _ = _ := by 
              ring
        rw [aux2]
        ring
      rw [h7]
      simp [Nat.gcd_mul_left]
      
    rw [h5, h6]
  calc
    Nat.lcm (x ^ 4 - 1) (x ^ 5 + 1)
        = (x ^ 4 - 1) * (x ^ 5 + 1) / Nat.gcd (x ^ 4 - 1) (x ^ 5 + 1) := by rw [Nat.lcm]
    _ = (x ^ 4 - 1) * (x ^ 5 + 1) / (x + 1) := by rw [h3]
    _ = (x - 1) * (x ^ 2 + 1) * (x ^ 5 + 1) := by
      have h7 : x ^ 4 - 1 = (x - 1) * (x + 1) * (x ^ 2 + 1) := by
        ring_nf
        zify
        have aux1 : ↑(x ^ 4 - 1 : ℕ) = (x : ℤ)^ 4 - 1:= by 
          have pos :  x ^ 4 ≥ 1 := by
            linarith
          norm_cast
        have aux2 : ↑(x - 1 : ℕ) = ((x : ℤ) - 1) := by 
          have pos : x ≥ 1 := by 
            linarith 
          norm_cast
        rw [aux1, aux2]
        ring_nf
      rw [h7]
      have aux1 : (x - 1) * (x + 1) * (x ^ 2 + 1) * (x ^ 5 + 1) / (x + 1) = (x - 1) * (x ^ 2 + 1) * (x ^ 5 + 1) := by
        have aux2 : (x - 1) * (x + 1) * (x ^ 2 + 1) * (x ^ 5 + 1) / (x + 1) = 
          ((x - 1)  * (x ^ 2 + 1) * (x ^ 5 + 1))* (x + 1) / (x + 1) := by 
          ring_nf
        rw [aux2]
        refine (nat_div_eq_iff ?_).mpr ?_
        linarith
        constructor
        simp
        have aux4 : (x - 1) * (x ^ 2 + 1) * (x ^ 5 + 1) * (x + 1) + (x + 1) - 1 
          = (x - 1) * (x ^ 2 + 1) * (x ^ 5 + 1) * (x + 1) + ((x + 1) - 1) := by 
          omega
        have aux3 : (x + 1) - 1 ≥ 0 := by 
          omega
        linarith
      rw [aux1]
  
      