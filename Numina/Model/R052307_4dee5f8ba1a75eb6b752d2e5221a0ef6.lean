import Mathlib

theorem number_theory_180374 :
    Set.ncard {n : ℕ | 2009 < n ∧ n / 57 = n % 57} = 22 := by
  have h1 : {n : ℕ | 2009 < n ∧ n / 57 = n % 57} = Finset.filter (λ n => 2009 < n ∧ n / 57 = n % 57) (Finset.Icc 0 3500) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide