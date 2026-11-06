import Mathlib

theorem algebra_186254 (n : ℕ) : ∑ i in Finset.Icc 1 (n - 1), i * (i + 1) = n * (n + 1) * (n - 1) / 3 := by 
  have h1 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 (n - 1), i * (i + 1) = n * (n + 1) * (n - 1) / 3 := by
    intro n 
    induction n with
    | zero => 
      simp
    | succ n ih =>
      cases n with 
      | zero => 
        simp
      | succ n => 
        cases n with 
        | zero => 
          simp
        | succ n => 
          simp [Finset.sum_Icc_succ_top, mul_add, add_mul] at ih ⊢ 
          <;> ring_nf at ih ⊢ 
          <;> omega 
  specialize h1 n 
  simpa using h1