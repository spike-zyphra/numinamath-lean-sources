import Mathlib

theorem number_theory_246972 :
    Set.ncard {x : ℚ | x < 1 ∧ ∃ n d : ℕ, x = n / d ∧ n ∈ Finset.Icc 1 9 ∧ d ∈ Finset.Icc 1 9} = 27 := by
  have h1 : {x : ℚ | x < 1 ∧ ∃ n d : ℕ, x = n / d ∧ n ∈ Finset.Icc 1 9 ∧ d ∈ Finset.Icc 1 9} = Finset.image (fun p : ℕ × ℕ => ((p.1 : ℚ) / (p.2 : ℚ))) (Finset.filter (fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ) < 1) (Finset.Icc 1 9 ×ˢ Finset.Icc 1 9)) := by
    ext x
    simp
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide