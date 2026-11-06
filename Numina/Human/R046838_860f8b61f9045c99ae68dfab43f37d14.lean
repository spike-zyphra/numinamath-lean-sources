import Mathlib

theorem number_theory_47233 : IsGreatest {n : ℤ | n < 103 ∧ 103 ∣ n ^ 3 - 1} 56 := by
  constructor
  · norm_num
  . intro n ⟨h₁, h₂⟩
    contrapose! h₂
    suffices H : ∀ n ∈ Finset.Ioo (56 : ℤ) 103, ¬ 103 ∣ n ^ 3 - 1 from H n (Finset.mem_Ioo.2 ⟨h₂, h₁⟩)
    native_decide
