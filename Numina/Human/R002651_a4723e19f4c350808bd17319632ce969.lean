import Mathlib

/-
Mr. Jones has eight children of different ages. On a family trip his oldest child, who is 9, spots a license plate with a 4-digit number in which each of two digits appears two times. "Look, daddy!" she exclaims. "That number is evenly divisible by the age of each of us kids!" "That's right," replies Mr. Jones, "and the last two digits just happen to be my age." Which of the following is not the age of one of Mr. Jones's children?

(A) 4 (B) 5 (C) 6 (D) 7 (E) 8
-/

theorem AMC_Number_Theory_1170
  (age : Finset ℕ) -- of different ages
  (hal : age.card = 8) -- Mr. Jones has eight children
  (hamn : age.min = 1) -- ages are positive
  (ham : age.max = 9) -- oldest child, who is 9
  (a b c d : Fin 10)
  (plate : List (Fin 10))
  (platen : ℕ)
  (hpn : platen = 1000*a + 100*b + 10*c + d) -- opting for reconstruction rather than invoking `Nat.digits` since we are fixed-width
  (hpl : plate = [a, b, c, d]) -- 4-digit number plate
  (hpc : ∀ i ∈ plate, plate.count i = 2) -- each of two digits appears two times
  (hpd : ∀ i ∈ age, i ∣ platen) -- That number is evenly divisible by the age of each of us kids
  (hpt : platen % 100 ≠ 0) -- and the last two digits just happen to be my age (which is non-negative by assumption in `hap` too)
  : ¬(5 ∈ age)
  
  := by
  by_cases hac : ¬(5 ∈ age)
  . exact hac
  -- There are nine possible ages out of eight children, so there cannot be two ages less than the max age (9) that doesn't exist in the family simultaneously.
  have h2notin : ∀ (a b : ℕ) (hal : 1 ≤ a) (hau : a ≤ 9) (hbl : 1 ≤ b) (hbu : b ≤ 9) (hab : a ≠ b), a ∈ age ∨ b ∈ age := by
    intro a b hal hau hbl hbu hab
    -- We proceed by contradiction
    by_cases haec1 : a ∈ age
    . left
      exact haec1
    by_cases haec2 : b ∈ age
    . right
      exact haec2
    -- There are only 7 valid ages
    let dom : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9} \ {a, b}
    have hsub : age ⊆ dom := by
      have hsub1 : ∀ (i : ℕ), i ∈ age → i ∈ dom := by
        intro i hi
        have hiu : i ≤ 9 := by
          apply Finset.le_max_of_eq hi
          exact ham
        have hiu : 1 ≤ i := by
          apply Finset.min_le_of_eq hi
          exact hamn
        by_cases hsub1a : i = a
        . rw [hsub1a] at hi
          contradiction
        by_cases hsub1b : i = b
        . rw [hsub1b] at hi
          contradiction
        interval_cases i
        all_goals {
          simp [dom]
          constructor
          exact hsub1a
          exact hsub1b
        }
      rw [Finset.subset_iff]
      exact hsub1
    -- Which is not enough for 8 children
    have hcard : age.card ≤ 7 := by
      have hdomc : dom.card = 7 := by
        have hsub : ({a, b} : Finset ℕ) ⊆ {1, 2, 3, 4, 5, 6, 7, 8, 9} := by
          intros h hx
          simp at hx
          rcases hx with hx | hx
          . interval_cases a
            all_goals {
              rw [hx]
              simp
            }
          . interval_cases b
            all_goals {
              rw [hx]
              simp
            }
        rw [Finset.card_sdiff hsub]
        simp [Finset.card_pair hab]
      rw [← hdomc]
      apply Finset.card_le_card
      exact hsub
    linarith
  -- We proceed with a proof by contradiction
  -- We can now show that the number plate ends in 0 (by divisibility of 2*5 = 10)
  have hld : d = 0 := by
    -- We first show that there is an even number in `age`
    have h2div : 2 ∣ platen := by
      rcases h2notin 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) with h2 | h4
      . exact hpd 2 h2
      . have h4 := hpd 4 h4
        omega
    simp at hac
    -- And we already assumed for the sake of contradiction that there is a 5 in `age`
    have h5div := hpd 5 hac
    -- So 10 divides the number plate
    have h10div : 10 ∣ platen := by omega
    -- Hence, our final digit, `d`, is 0
    have hud : 0 = (d : ℕ) % 10 := by omega
    omega
  -- We now case bash the possibible locations of the other 0
  have h0 : 0 ∈ plate := by
    rw [hpl, hld]
    simp
  by_cases hcase0 : a = 0
  -- In the case, the plate is 0bb0, because all digits appear twice
  . have hne : b ≠ 0 := by
      by_cases hneg : b ≠ 0
      . exact hneg
      simp at hneg
      absurd hpc
      push_neg
      exists 0
      constructor
      . exact h0
      have hneg1 : plate.count 0 ≥ 3 := by
        specialize hpc 0 h0
        rw [hpl]
        simp [List.count]
        repeat rw [List.countP_cons]
        simp [hcase0, hneg, hld]
      linarith
    have heq : b = c := by
      by_cases hneg : b = c
      . exact hneg
      absurd hpc
      push_neg
      exists b
      constructor
      . rw [hpl]
        simp
      have hneg1 : plate.count b ≤ 1 := by
        specialize hpc b (by rw [hpl]; simp : b ∈ plate)
        rw [hpl]
        simp [List.count]
        repeat rw [List.countP_cons]
        simp [(by rw [hld]; symm; exact hne : d ≠ b),
              (by symm; exact hneg : c ≠ b),
              (by rw [hcase0]; push_neg; symm; exact hne : ¬a = b)]
      linarith
    -- Using the divisibility rule for 9 (we know for sure that 9 is a factor), we get that `b` must be a multiple of 9
    have h9mul : (b : ℕ) % 9 = 0 := by
      have hplmod : platen % 9 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        apply hpd
        apply Finset.mem_of_max
        exact ham
      rw [hpn] at hplmod
      omega
    -- However, the two possibilities for `Fin 10` are 0 and 9, but 0 cannot occur because we have already established 2 zeroes
    have h9 : b = 9 := by
      have hub : (b : ℕ) ≤ 9 := Fin.is_le (b : Fin 10)
      interval_cases hic : (b : ℕ)
      any_goals contradiction
      . have hic : b = 0 := by omega
        contradiction
      omega
    -- We now know the resulting number
    have his : platen = 990 := by
      omega
    -- Which is bad, because neither 4 and 7 could be valid ages now
    rcases h2notin 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) with h4 | h7
    . have hneg : 4 ∣ platen := hpd 4 h4
      omega
    . have hneg : 7 ∣ platen := hpd 7 h7
      omega
  by_cases hcase1 : b = 0
  -- In the case, the plate is a0a0, because all digits appear twice, and we do the same proof as before
  . have hne : a ≠ 0 := by
      by_cases hneg : a ≠ 0
      . exact hneg
      simp at hneg
      absurd hpc
      push_neg
      exists 0
    have heq : a = c := by
      by_cases hneg : a = c
      . exact hneg
      absurd hpc
      push_neg
      exists a
      constructor
      . rw [hpl]
        simp
      have hneg1 : plate.count a ≤ 1 := by
        specialize hpc a (by rw [hpl]; simp : a ∈ plate)
        rw [hpl]
        simp [List.count]
        omega
      linarith
    -- In a very similar fashion, we conclude that number plate is 9090
    have h9mul : (a : ℕ) % 9 = 0 := by
      have hplmod : platen % 9 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        apply hpd
        apply Finset.mem_of_max
        exact ham
      rw [hpn] at hplmod
      omega
    have h9 : a = 9 := by
      have hub : (a : ℕ) ≤ 9 := Fin.is_le (a : Fin 10)
      interval_cases hic : (a : ℕ)
      any_goals contradiction
      . have hic : a = 0 := by omega
        contradiction
      omega
    have his : platen = 9090 := by
      omega
    -- Which is bad again, because neither 4 and 7 could be valid ages now
    rcases h2notin 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) with h4 | h7
    . have hneg : 4 ∣ platen := hpd 4 h4
      omega
    . have hneg : 7 ∣ platen := hpd 7 h7
      omega
  by_cases hcase2 : c = 0
  -- Ending in 00 violates the dad age constraint
  . absurd hpt
    rw [hpn, hld, hcase2]
    simp
    rw [(by norm_num : 1000 = 100 * 10)]
    rw [mul_assoc, Nat.mul_mod_right 100]
  -- One of the above cases must be true, as otherwise we have only one 0, which is a contradiction
  absurd hpc
  push_neg
  exists 0
  constructor
  . exact h0
  have hneg : plate.count 0 ≤ 1 := by
    specialize hpc 0 h0
    rw [hpl]
    simp [List.count]
    -- At this point we can just do the count by erasing digit by digit
    repeat rw [List.countP_cons]
    simp [hcase0, hcase1, hcase2, hld]
  linarith