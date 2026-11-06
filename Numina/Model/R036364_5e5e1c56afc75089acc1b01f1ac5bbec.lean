import Mathlib

open Nat Finset List

theorem number_theory_97342 {N : ℕ}
    (hN : N = (ofDigits 10 $ (List.Ico 19 93) |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) :
    IsGreatest {k | 3 ^ k ∣ N} 1 := by
  rw [IsGreatest]
  constructor
  · -- Show 1 is in {k | 3 ^ k ∣ N}
    rw [Set.mem_setOf_eq]
    rw [hN]
    native_decide
  · -- Show that 1 is greatest in the set
    intro k hk
    rw [Set.mem_setOf_eq] at hk
    rw [hN] at hk
    have h1 : k ≤ 1 := by
      have h2 : ∀ (k : ℕ), (3 ^ k ∣ (ofDigits 10 $ (List.Ico 19 93) |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) → k ≤ 1 := by
        intro k hk
        by_contra h
        push_neg at h
        have h3 : k ≥ 2 := by omega
        have h4 : ¬ (3 ^ 2 ∣ (ofDigits 10 $ (List.Ico 19 93) |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) := by
          native_decide
        have h5 : (3 ^ 2 ∣ (3 ^ k)) := by
          apply pow_dvd_pow _ (by omega)
        have h6 : (3 ^ 2 ∣ (ofDigits 10 $ (List.Ico 19 93) |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) := by
          exact dvd_trans h5 hk
        contradiction
      apply h2 k hk
    omega