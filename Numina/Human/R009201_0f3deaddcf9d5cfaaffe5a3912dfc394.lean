import Mathlib

theorem algebra_13890 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 9 ∣ n}.ncard = 10 := by 
  have : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 9 ∣ n} = Finset.filter (λ n => 9 ∣ n) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [this]
  rw [Finset.filter]
  simp [Finset.Icc]
  rfl -- Lean is able to compute the cardinality of the filtered set directly