import Mathlib

theorem number_theory_294634 :
    Set.ncard {n : ℕ | 100 ≤ n ∧ n ≤ 999 ∧ ∃ a b c, a = (n / 100) % 10 ∧ b = (n % 100) / 10 ∧ c = n % 10 ∧ a + c = 2 * b} = 45 := by
  have : {n : ℕ | 100 ≤ n ∧ n ≤ 999 ∧ ∃ a b c, a = (n / 100) % 10 ∧ b = (n % 100) / 10 ∧ c = n % 10 ∧ a + c = 2 * b} = Finset.filter (fun n => 100 ≤ n ∧ n ≤ 999 ∧ ( (n / 100) % 10 + (n % 10) = 2 * ((n % 100) / 10) ) ) (Finset.Icc 0 999) := by
    ext n
    simp
    <;> omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide