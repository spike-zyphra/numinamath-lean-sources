import Mathlib

theorem number_theory_639546 (E n : ℕ) (hE : E > 0) (hn : 3 * n = 999 ^ E) :
  n % 10 = if Even E then 7 else 3 := by 
  zify at hn
  have h1 : 3 * n ≡  (-1) ^ E [ZMOD 10]:= by 
    rw [hn]
    exact Int.ModEq.pow E rfl
  have h2 : 3 * n * 7 ≡ (- 1) ^ E * 7 [ZMOD 10] := by 
    exact Int.ModEq.mul h1 rfl
  have h3 : 3 * n * 7 ≡ n [ZMOD 10] := by 
    apply Int.modEq_of_dvd
    ring_nf
    omega
  have h4 : n ≡ (- 1) ^ E * 7 [ZMOD 10] := by 
    calc 
      _ ≡ 3 * n * 7 [ZMOD 10] := by 
        exact Int.ModEq.symm h3
      _ ≡ (- 1) ^ E * 7 [ZMOD 10] := by exact h2
  zify
  by_cases heven : Even E
  · rw [if_pos heven]
    unfold Int.ModEq at h4
    rw [h4]
    have aux : (-1) ^ E = 1 := by 
      exact Even.neg_one_pow heven
    rw [aux]
    omega
  · have hodd : Odd E := by 
      exact Nat.not_even_iff_odd.mp heven
    rw [if_neg heven]
    unfold Int.ModEq at h4
    rw [h4]
    have aux : (-1) ^ E = -1 := by
      exact Odd.neg_one_pow hodd
    rw [aux]
    omega