import Mathlib

def is_leap_year (n : ℕ) := n % 4 = 0 ∧ (n % 100 ≠ 0 ∨ n % 400 = 0)

theorem number_theory_284396 :
    Set.ncard {n | 2000 ≤ n ∧ n ≤ 4000 ∧ is_leap_year n} = 486 := by
  have h1 : {n | 2000 ≤ n ∧ n ≤ 4000 ∧ is_leap_year n} = Finset.filter (fun n => n % 4 = 0 ∧ (n % 100 ≠ 0 ∨ n % 400 = 0)) (Finset.Icc 2000 4000) := by
    ext n
    simp [is_leap_year, Finset.mem_Icc]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide