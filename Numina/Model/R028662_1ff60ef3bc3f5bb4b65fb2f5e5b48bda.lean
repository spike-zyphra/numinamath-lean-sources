import Mathlib

def is_stepstool_number (n : ℕ) := n.divisors.card + 1 = (n + 1).divisors.card

theorem number_theory_79868 :
    ∑ᶠ n ∈ {n | n < 300 ∧ is_stepstool_number n}, n = 687 := by 
  have h1 : {n | n < 300 ∧ is_stepstool_number n} = 
    Finset.filter (fun n => n.divisors.card + 1 = (n + 1).divisors.card) (Finset.Iio (300 : ℕ)) := by
    ext n
    simp [is_stepstool_number]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  native_decide