import Mathlib

open Real Finset
open scoped BigOperators 

theorem number_theory_636091 (L : ℕ) :
  (∑ k in Finset.range (L+1), (⌊(4^k / 5 : ℝ)⌋ : ℝ)) =
  (if Odd L then (4^(L+1) - 1)/(15 : ℝ) - (L + 1)/2 else (4^(L+1) - 4)/15 - L/2) := by 
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
  induction L with 
  | zero => 
    simp
    norm_num
  | succ n ih => 
    rw [range_add_one, sum_insert, ih]
    -- then discuss by cases of n odd and n even
    by_cases hodd : Odd n 
    -- the case n is odd
    · 
      have hodd2 : ¬ Odd (n + 1) := by 
        refine Nat.not_odd_iff_even.mpr ?_
        exact Odd.add_one hodd
      rw [if_pos hodd, if_neg hodd2]
      rw [h1, if_neg hodd2]
      field_simp
      ring 
    · -- the case n is even
      have hodd2 : Odd (n + 1) := by 
        simp at hodd
        exact Even.add_one hodd
      rw [if_neg hodd, if_pos hodd2]
      rw [h1, if_pos hodd2]
      field_simp
      ring
    simp
  