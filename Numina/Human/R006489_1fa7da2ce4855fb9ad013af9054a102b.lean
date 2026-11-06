import Mathlib

open Finset

lemma two_pow_div_three_odd (n : ℕ) (h : Odd n) : 3 ∣ (2 : ℤ) ^ n - 2 := by 
  obtain ⟨m, hm⟩ := h
  apply Int.ModEq.dvd 
  rw [hm, pow_add, pow_mul]
  have aux1 : (2 ^ 2) ^ m ≡ 1 [ZMOD 3] := by 
    have aux2 : (2 ^ 2) ≡ 1 [ZMOD 3] := by 
      rfl
    calc 
      _ ≡ (1) ^ m [ZMOD 3] := by
        exact Int.ModEq.pow m aux2
      _ ≡ 1 [ZMOD 3] := by 
        simp
  nth_rw 1 [show (2 : ℤ) = 1 * 2 ^ 1 by ring]
  exact Int.ModEq.mul (id (Int.ModEq.symm aux1)) rfl

lemma two_pow_div_three_even (n : ℕ) (h : Even n) : 3 ∣ (2 : ℤ) ^ n - 1 := by 
  obtain ⟨m, hm⟩ := h
  apply Int.ModEq.dvd 
  rw [hm, show m + m = 2 * m by ring, pow_mul]
  
  have aux2 : (2 ^ 2) ≡ 1 [ZMOD 3] := by 
    rfl
  apply Int.ModEq.symm
  calc 
    _ ≡ (1) ^ m [ZMOD 3] := by
      exact Int.ModEq.pow m aux2
    _ ≡ 1 [ZMOD 3] := by 
      simp
  

theorem number_theory_637639 (K : ℕ) (hK : K > 0) :
  ∑ i ∈ Finset.range K, ⌊(2 ^ i / 3 : ℝ)⌋ = if Odd K then ((2 : ℤ) ^ K - 2) / 3 - (K - 1) / 2
  else ((2 : ℤ) ^ K - 1) / 3 - K / 2 := by 
  -- use induction to prove this theorem
  induction' hK with n ih1 ih2
  · simp
    linarith
  · by_cases oddn : Odd n
    -- the case n is odd
    · simp [oddn] at ih2
      simp at ih1 ⊢ 
      have heven : Even (n + 1) := by 
        simp [oddn]
      have notodd :  ¬ Odd (n + 1):= by
        simp [heven]
      rw [if_neg notodd]
      have seteq : range (n + 1) = insert n (range n):= by
        exact range_add_one
      rw [seteq, sum_insert, ih2]
      obtain ⟨m, hm⟩ := two_pow_div_three_odd n oddn
      obtain ⟨t, ht⟩ := two_pow_div_three_even (n + 1) heven
      rw [hm, ht]
      have eq1 : (2 : ℤ) ^ n = 3 * m + 2 := by 
        linarith 
      have eq2 : (2 : ℝ) ^ n = 3 * m + 2 := by 
        norm_cast
        norm_cast at eq1
      have aux1 : ⌊ (2 : ℝ) ^ n / 3 ⌋ = m := by 
        rw [eq2]
        refine Int.floor_eq_iff.mpr ?_
        constructor 
        · refine (le_div_iff₀ ?_).mpr ?_ 
          linarith
          norm_cast
          linarith
        · refine (div_lt_iff₀ ?_).mpr ?_ 
          linarith
          norm_cast
          linarith
      rw [aux1]
      have eq3 : (2 : ℤ) ^ (n + 1) = 3 * t + 1 := by 
        linarith
      rw [pow_add, eq1] at eq3
      have teq : t = 2 * m + 1 := by 
        linarith
      rw [teq]
      field_simp
      have eq4 : ((n : ℤ) + 1) / 2 = (n - 1) /2 + 1 := by 
        obtain ⟨s, hs⟩ := oddn
        rw [hs]
        omega
      rw [eq4]
      ring_nf
      simp 
    · -- the case n is even
      have oddnsucc : Odd (n + 1) := by 
        exact Nat.odd_add_one.mpr oddn
      simp [oddn] at ih2
      simp [oddnsucc]
      have seteq : range (n + 1) = insert n (range n):= by
        exact range_add_one
      rw [seteq, sum_insert, ih2]
      simp at oddn
      obtain ⟨m, hm⟩ := two_pow_div_three_even n oddn
      obtain ⟨t, ht⟩ := two_pow_div_three_odd (n + 1) oddnsucc
      have eq1 : ⌊(2 : ℝ) ^ n / 3⌋ = m := by 
        have aux1 : (2 : ℝ) ^ n = 3 * m + 1 := by 
          have aux2 : (2 : ℤ) ^ n = 3 * m + 1 := by 
            linarith
          norm_cast at aux2
          norm_cast
        rw [aux1]
        refine Int.floor_eq_iff.mpr ?_
        constructor
        · refine  (le_div_iff₀ ?_).mpr ?_
          · linarith
          · norm_cast 
            linarith
        · refine (div_lt_iff₀ ?_).mpr ?_ 
          · linarith
          · norm_cast
            linarith
      rw [eq1, hm, ht]
      have eq2 : (2 : ℤ) ^ (n + 1) = 3 * t + 2 := by 
        linarith
      have eq3 : (2 : ℤ) ^ n = 3 * m + 1 := by 
        linarith
      rw [pow_add, eq3] at eq2
      have teq : t = 2 * m := by
        linarith
      rw [teq]
      omega
      simp