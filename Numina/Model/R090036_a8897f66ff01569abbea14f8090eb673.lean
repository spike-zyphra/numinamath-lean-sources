import Mathlib

theorem algebra_10378 : {n : ℤ | (n - 2) * (n + 4) < 0} = {n | n ∈ Set.Ioo (-4) 2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Forward direction: (n - 2)(n + 4) < 0 implies -4 < n < 2
    intro h
    cases mul_neg_iff.mp h with
    | inl h_pos_neg =>
      omega -- This will derive contradiction
    | inr h_neg_pos =>
      constructor
      · linarith -- Solving n + 4 > 0 to -4 < n
      · linarith -- Solving n - 2 < 0 to n < 2
  · -- Reverse direction: -4 < n < 2 implies (n - 2)(n + 4) < 0
    rintro ⟨h1, h2⟩
    have h3 : n + 4 > 0 := by linarith
    have h4 : n - 2 < 0 := by linarith
    nlinarith -- Multiply them and prove it's negative