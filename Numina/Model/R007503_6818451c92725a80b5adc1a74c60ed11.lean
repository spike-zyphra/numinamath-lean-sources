import Mathlib

theorem number_theory_15276  :
  IsGreatest {n | 9^2 ≤ n^2 ∧ n^2 < 9^3} 26 ∧ 26 = Nat.ofDigits 9 [8, 2] := by
  constructor
  · -- We need to show 26 is the greatest integer in the set
    constructor
    · -- Show 26 is in the set {n | 9^2 ≤ n^2 ∧ n^2 < 9^3}
      constructor
      · norm_num
      · norm_num
    · -- Show that for any n in the set, n ≤ 26
      intro n hn
      have h₁ : 9^2 ≤ n^2 := hn.1
      have h₂ : n^2 < 9^3 := hn.2
      by_contra h
      push_neg at h
      have h3 : n ≥ 27 := by
        nlinarith
      nlinarith -- contradiction
  · -- Show 26 equals the base 9 number represented by digits [8, 2]
    norm_num [Nat.ofDigits]