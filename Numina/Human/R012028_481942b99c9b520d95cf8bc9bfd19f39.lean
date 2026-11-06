import Mathlib

/-
The sequence of positive integers $a_n$ satisfies $a_1 = 3$, $a_2 = 7$, $a_3 = 25$, and $a_{n+3} = 3a_{n+2} - 4a_n$. Find the remainder when $a_{2021}$ is divided by $2021$.
-/

theorem number_theory_622313 (a : ℕ → ℤ)  (ha1 : a 1 = 3) (ha2 : a 2 = 7) (ha3 : a 3 = 25) (h: ∀n≥1, a (n+3) = 3 * a (n+2) - 4 * a n): a 2021 % 2021 = 1 := by 

  --We calculate the formula for a n by induction.
  --We have a n = n*2^n + (-1)^(n+1).
  have : ∀n≥1, a n = n*2^n + (-(1:ℤ))^(n+1) := by 
    have : ∀x:ℕ, ∀ m≤x, a (m+1) = (m+1)*2^(m+1) + (-(1:ℤ))^(m+1+1) := by 
      intro x 
      induction' x with x hx
      
      simp [ha1]

      intro m hm
      by_cases mlex : m ≤ x
      apply hx
      exact mlex
      have mexp1 : m = x+1 := by omega
      rw [mexp1]

      by_cases xe0: x = 0
      rw [xe0]
      simp [ha2]
      by_cases xe1: x = 1
      rw [xe1]
      simp [ha3]
      have xge2: 2 ≤ x := by omega
      have xm1ge1 : x-1 ≥ 1 := by omega
      have : x + 1 + 1 = x-1+3 := by omega
      rw [this]
      specialize h (x-1) (by linarith)
      rw [h]
      have t1 : a (x - 1 + 2)  = (x+1)*2^(x+1) + (-1:ℤ)^(x+2) := by 
        have : x-1+2 = x-1+1+1 := by omega
        rw [this]
        specialize hx (x-1+1)
        have tmp : x-1+1 ≤ x := by omega
        apply hx at tmp
        rw [tmp]
        field_simp
        have : @HAdd.hAdd ℕ ℕ ℕ instHAdd (x - 1 + 1) 1 = x+1 := by omega
        rw [this]

        
      have t2 : a (x - 1) = (x-1)*2^(x-1) + (-1:ℤ)^x := by 
        have : x-1 = x-2+1 := by omega
        rw [this]
        specialize hx (x-2)
        have tmp : x-2 ≤ x := by omega
        apply hx at tmp
        rw [tmp]
        field_simp
        have : @HAdd.hAdd ℤ ℤ ℤ instHAdd (↑x - 2) 1 = x-1 := by omega
        rw [this]
        have : x - 2 + 1 + 1 = x := by omega
        rw [this]

      rw [t1,t2]
      field_simp
      ring_nf
      have : (2:ℤ) ^ x = 2^(x-1) * 2 := by 
        rw [← pow_succ]
        have : x-1+1 = x := by omega
        rw [this]
      rw [this]
      have : (-(1:ℤ)) ^ x = -(-1) ^ (x-1) := by
        have : (-(1:ℤ)) ^ x = (-1) ^ (x-1) * (-1) := by 
          rw [←pow_succ]
          have : x-1+1=x := by omega
          rw [this]
        rw [this]
        simp
      rw [this]
      ring_nf
      
    intro n hn
    have exi : ∃ k:ℕ, k + 1 = n := by use n-1; omega
    obtain ⟨k,hk⟩ := exi
    specialize this k k
    norm_cast at this
    rw [hk] at this
    rw [this]
    simp
    linarith
  
  -- Then we find that a 2021 mod 2021 = 1 by using the formula of a n.
  have ha2021: a 2021 = 2021*2^2021 + (-(1:ℤ))^(2022) := by apply this; linarith
  rw [ha2021]

  have tar : (2021 * 2 ^ 2021 + (-1) ^ 2022) ≡ 1 [ZMOD 2021] := by 
    have tar1 : 2021 * 2 ^ 2021 ≡ 0 [ZMOD 2021] := by 
      have : 2021 ∣ (2021:ℤ) * 2 ^ 2021 := by use 2^2021
      apply Dvd.dvd.modEq_zero_int
      exact this
      
    have tar2 : (-(1:ℤ)) ^ 2022 ≡ 1 [ZMOD 2021] := by 
      have : Even 2022 := by use 1011;
      have : (-(1:ℤ)) ^ 2022 = 1 := by 
        rw [neg_one_pow_eq_one_iff_even]; 
        exact this
        norm_num
      rw [this]
      

    exact Int.ModEq.add tar1 tar2
    
  rw [Int.ModEq] at tar
  have : (1:ℤ) % 2021 = 1 := by norm_num
  rw [this] at tar
  exact tar

