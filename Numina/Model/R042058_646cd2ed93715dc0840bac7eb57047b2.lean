import Mathlib

theorem number_theory_144645 : {i ∈ Finset.Icc 1 2017 | (i * (i + 1)) % 10 = 0}.card = 806 := by
  have h1 : {i ∈ Finset.Icc 1 2017 | (i * (i + 1)) % 10 = 0} = Finset.filter (fun i => (i * (i + 1)) % 10 = 0) (Finset.Icc 1 2017) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> native_decide