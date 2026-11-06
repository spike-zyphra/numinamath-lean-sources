import Mathlib

open Nat Set

theorem number_theory_98579 :
Set.ncard {k | 0 < k ∧ ∃ n, 1 + k * n = 2005} = 12 := by
  have h1 : {k | 0 < k ∧ ∃ n, 1 + k * n = 2005} = Nat.divisors 2004 := by
    ext k
    simp
    constructor
    · -- First direction: if k >0 and exists n s.t.1 +k * n =2005 then k divides 2004
      rintro ⟨hk1, ⟨n, hn⟩⟩
      have hk2 : k ∣ 2004 := by
        use n
        all_goals nlinarith
      exact hk2
    · -- Second direction: if k divides 2004 then k >0 and exists n s.t.1 + k * n =2005
      intro hk2
      constructor
      · -- Show k > 0
        by_contra h
        push_neg at h
        have h2 : k = 0 := by nlinarith
        rw [h2] at hk2
        all_goals simp at hk2
      · -- Show ∃ n, 1 + k * n = 2005
        have h2 : k ∣ 2004 := by
          exact_mod_cast hk2
        rcases h2 with ⟨c, hc⟩
        use c
        all_goals nlinarith
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide