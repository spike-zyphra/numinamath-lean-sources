import Mathlib

theorem number_theory_101857 :
  IsGreatest {x : ℤ | ∑ i ∈ Finset.Icc 1 10, ⌊(x : ℚ) / (Nat.factorial i)⌋ = 1001} 584 := by

  refine ⟨by native_decide, ?_⟩
  unfold upperBounds
  simp
  intro x hx
  by_contra h_contra
  replace h_contra : (585:ℚ) ≤ x := by norm_cast; omega


  let f: ℚ → ℤ := fun x => ∑ i ∈ Finset.Icc 1 10, ⌊x / (Nat.factorial i)⌋
  have hf_mono : Monotone f := by
    intro x y hxy
    simp only [f]
    apply Finset.sum_le_sum
    intro i hi
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right hxy
    simp [Nat.cast_pos]

  have := hf_mono h_contra
  unfold f at this
  rw [hx] at this
  contrapose this
  native_decide
