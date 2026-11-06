import Mathlib

def isLucky (m : ℕ) : Prop :=
  m < 2012 ∧ (Nat.digits 10 m).sum ≡ 0 [MOD 6] ∧ m ≡ 0 [MOD 6]

theorem number_theory_301704 : {m | isLucky m}.encard = 168 := by
  have h1 : {m | isLucky m} = Finset.filter (fun m => m < 2012 ∧ (Nat.digits 10 m).sum ≡ 0 [MOD 6] ∧ m ≡ 0 [MOD 6]) (Finset.Iio (2012 : ℕ)) := by
    ext m
    simp [isLucky, Finset.mem_filter, Finset.mem_Iio]
    all_goals omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide