import Mathlib

open Finset 

theorem number_theory_639588 (M : ℕ) : 
  ∑ k ∈ Icc 0 M, ⌊(4 ^ k / 5 : ℝ)⌋ = (2 * 4 ^ (M + 1) - 15 * M - 8 - 9 * ((M : ℤ) % 2) : ℤ) / (30 : ℝ) := by 
  -- first prove that for odd and even n we have the explicit expression for (⌊(4 ^ n / 5 : ℝ)⌋ : ℝ)
  have h1 :∀ (n : ℕ), (⌊(4 ^ n / 5 : ℝ)⌋ : ℝ) = if Odd n then (4 ^ n / 5 : ℝ) - 4 / 5 
    else (4 ^ n / 5 : ℝ) - 1 / 5 := by 
    intro n
    by_cases hodd : Odd n
    · 
      have dvd1 : (5 : ℤ) ∣ 4 ^ n - 4 := by 
        obtain ⟨s, hs⟩ := hodd
        rw [hs]
        apply Int.ModEq.dvd
        rw [pow_add, pow_mul]
        apply Int.ModEq.symm 
        calc 
          _ ≡ 1 ^ s * 4 [ZMOD 5] := by 
            refine Int.ModEq.mul ?_ rfl
            exact Int.ModEq.pow s rfl
          _ ≡ 4 [ZMOD 5] := by
            simp
      obtain ⟨t, ht⟩ := dvd1
      have aux1 : (4 ^ n : ℝ) = 5 * ↑t + 4 := by
        norm_cast
        norm_num
        omega
      rw [if_pos hodd]
      rw [aux1]
      have aux2 : ⌊(5 * (t : ℝ) + 4) / 5⌋ = t := by 
        refine Int.floor_eq_iff.mpr ?_
        constructor
        · refine (le_div_iff₀ ?_).mpr ?_ 
          linarith
          norm_cast
          linarith
        · refine (div_lt_iff₀ ?_).mpr ?_
          linarith
          linarith
      rw [aux2]
      field_simp
    · -- the case n is even 
      simp at hodd
      have dvd1 : (5 : ℤ) ∣ 4 ^ n - 1 := by 
        obtain ⟨s, hs⟩ := hodd
        rw [hs]
        apply Int.ModEq.dvd
        rw [show s + s = 2 * s by ring, pow_mul]
        apply Int.ModEq.symm 
        calc 
          _ ≡ 1 ^ s [ZMOD 5] := by 
            exact Int.ModEq.pow s rfl
          _ ≡ 1[ZMOD 5] := by
            simp
      obtain ⟨t, ht⟩ := dvd1
      have aux1 : (4 ^ n : ℝ) = 5 * ↑t + 1 := by
        norm_cast
        norm_num
        omega
      rw [if_neg]
      rw [aux1]
      have aux2 : ⌊(5 * (t : ℝ) + 1) / 5⌋ = t := by 
        refine Int.floor_eq_iff.mpr ?_
        constructor
        · refine (le_div_iff₀ ?_).mpr ?_ 
          linarith
          norm_cast
          linarith
        · refine (div_lt_iff₀ ?_).mpr ?_
          linarith
          linarith
      rw [aux2]
      field_simp
      exact Nat.not_odd_iff_even.mpr hodd
  norm_num
  -- with the above formula, we could use induction to prove the theorem.
  induction M with 
  | zero => 
    simp 
    norm_num
  | succ m ih => 
    have seteq1 : Icc 0 (m + 1) = insert (m + 1) (Icc 0 m) := by 
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    rw [seteq1, sum_insert, ih, h1 (m + 1)]
    by_cases hodd : Odd (m + 1)
    · 
      rw [if_pos hodd]
      have eq1 : (m : ℤ) % 2 = 0 := by 
        obtain ⟨t, ht⟩ := hodd
        have meq : m = 2 * t := by omega
        rw [meq]
        simp
      have eq2 : ((m + 1 : ℕ) : ℤ) % 2 = 1 := by 
        obtain ⟨t, ht⟩ := hodd
        have meq : m = 2 * t := by omega
        rw [meq]
        omega
      rw [eq1, eq2]
      field_simp
      ring
    -- the case m + 1 is even
    · 
      rw [if_neg hodd]
      have eq1 : (m : ℤ) % 2 = 1 := by 
        simp at hodd
        obtain ⟨t, ht⟩ := hodd
        have meq : m = 2 * t - 1 := by omega
        rw [meq]
        omega
      have eq2 : ((m + 1 : ℕ) : ℤ) % 2 = 0 := by 
        simp at hodd
        obtain ⟨t, ht⟩ := hodd
        have meq : m = 2 * t - 1 := by omega
        rw [meq]
        omega
      rw [eq1, eq2]
      field_simp 
      ring
    simp