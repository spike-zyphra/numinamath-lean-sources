import Mathlib

open scoped BigOperators
open Set

-- add an assumption at a 0 = 1,  complete `a` to be a function from ℕ → ℤ
theorem number_theory_641094 (K : ℕ) (a : ℕ → ℤ) (hK : K > 0)
  (ha0 : a 0 = 1) (ha1 : a 1 = 1) (han : ∀ n > 1, a n = ⌊(n ^ 3 : ℝ) / a (n - 1)⌋) :
  a K = if Odd K then K else (if K = 2 then 8 else K ^ 2 + K + 1) := by
  -- first we prove that forall k, a k > 0
  have aneq_and_pos : ∀ n, (a n = if Odd n then n else (if n = 2 then 8 else n ^ 2 + n + 1)) ∧ a n > 0 := by 
    intro n
    induction n with 
    | zero =>
      constructor
      simp [ha0]
      linarith
    | succ k ih => 
      by_cases hk0 : k = 0 
      · -- the case k = 0
        rw [hk0]
        simp [ha1]
      · -- the case k > 0
        have kgt0 : k > 0 := Nat.zero_lt_of_ne_zero hk0
        obtain ⟨ih1, ih2⟩ := ih
        by_cases hk1 : k = 1
        · -- the case k = 1
          rw [hk1]; simp [ha1]
          have notodd : ¬ Odd 2 := by 
            simp
          rw [if_neg notodd]
          rw [han 2 (by linarith)]
          simp [ha1]
          constructor
          refine Int.floor_eq_iff.mpr ?_
          constructor
          · norm_cast
          · norm_cast
          · refine Int.floor_pos.mpr ?_
            linarith
        · -- the case k = 2 
          by_cases hk2 : k = 2
          · rw[hk2]
            simp
            simp [hk2] at ih1
            have notodd : ¬ Odd 2 := by 
              simp
            rw [if_neg notodd] at ih1
            rw [han 3 (by linarith)]
            simp [ih1]
            have odd3 : Odd 3 := by 
              use 1
              norm_num
            rw [if_pos odd3]
            constructor
            refine Int.floor_eq_iff.mpr ?_
            constructor
            · norm_cast
              linarith
            · norm_cast
              linarith
            · refine Int.floor_pos.mpr ?_
              linarith
          · -- the case k ≥ 3
            have kge3 : k ≥ 3 := by 
              omega
            by_cases hkodd : Odd k
            -- the case k is odd
            · simp [hkodd] at ih1
              have even_aux : Even (k + 1) := by 
                exact Odd.add_one hkodd
              have notodd : ¬ Odd (k + 1) := by 
                exact Nat.not_odd_iff_even.mpr even_aux
              simp [notodd, hk1, han (k + 1) (by linarith)]
              constructor
              refine Int.floor_eq_iff.mpr ?_
              constructor
              · refine (le_div_iff₀ ?_).mpr ?_ 
                · norm_cast
                · norm_num
                  rw [ih1]
                  ring_nf
                  norm_cast
                  linarith
              · refine (div_lt_iff₀ ?_).mpr ?_ 
                · norm_cast
                · rw [ih1]
                  ring_nf
                  norm_cast
                  linarith
              · refine Int.floor_pos.mpr ?_
                rw [ih1]
                refine (le_div_iff₀ ?_).mpr ?_
                norm_cast
                norm_cast
                simp
                ring_nf
                omega
            · -- the case k is even
              have oddksucc : Odd (k + 1) := by 
                exact Nat.odd_add_one.mpr hkodd
              rw [if_pos oddksucc]
              have hkeven : Even k := by 
                simp at hkodd
                exact hkodd
              rw [if_neg hkodd, if_neg hk2] at ih1
              simp [han (k + 1) (by linarith)]
              constructor
              refine Int.floor_eq_iff.mpr ?_
              constructor
              · refine (le_div_iff₀ ?_).mpr ?_ 
                · norm_cast
                · norm_num
                  rw [ih1]
                  ring_nf
                  norm_cast
                  nlinarith
              · refine (div_lt_iff₀ ?_).mpr ?_ 
                · norm_cast
                · rw [ih1]
                  ring_nf
                  norm_cast
                  linarith
              · refine Int.floor_pos.mpr ?_
                rw [ih1]
                refine (le_div_iff₀ ?_).mpr ?_
                norm_cast
                omega
                norm_cast
                nlinarith
  exact (aneq_and_pos K).1