import Mathlib

theorem number_theory_307791 :
    ∃ n, ∑ i ∈ Finset.range 64, (n + i) = 2123456 ∨
    ∃ n, ∑ i ∈ Finset.range 128, (n + i) = 2123456 := by
  have h2 : ∃ n, ∑ i ∈ Finset.range 128, (n + i) = 2123456 := by
    use 16526
    native_decide
  refine' ⟨0, Or.inr h2⟩