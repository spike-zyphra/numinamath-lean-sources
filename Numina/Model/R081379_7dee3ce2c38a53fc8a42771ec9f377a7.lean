import Mathlib

theorem number_theory_180294 : {n : ℕ | n > 1 ∧ n ≤ 988000 ∧ 49 ∣ n}.encard = 20163 := by
  have h1 : {n : ℕ | n > 1 ∧ n ≤ 988000 ∧ 49 ∣ n} = Finset.filter (λ n => n > 1 ∧ 49 ∣ n) (Finset.Iic 988000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Iic]
  <;> try native_decide