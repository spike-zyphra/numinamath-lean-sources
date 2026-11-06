import Mathlib

theorem algebra_310356 (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ)
    (h₀ : ∑ j : Fin n, a j * Real.cos (α j) = 0)
    (h₁ : ∑ j : Fin n, a j * Real.cos (α j + 1) = 0) :
    ∑ j : Fin n, a j * Real.cos (α j + Real.pi / 10) = 0 := by 
  have eq1 : ∀ j : Fin n, a j * Real.cos (α j + 1) = a j * (Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1) := by 
    intro j 
    have eq2 : Real.cos (α j + 1) = Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1 := by 
      rw [Real.cos_add]
    rw [eq2] 
    <;> ring
  have eq2 : ∑ j : Fin n, a j * Real.cos (α j + 1) = ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1) := by 
    apply Finset.sum_congr 
    · rfl 
    · intro j _ 
      exact eq1 j
  rw [eq2] at h₁
  have eq3 : ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1) =
    Real.cos 1 * (∑ j : Fin n, a j * Real.cos (α j)) - Real.sin 1 * (∑ j : Fin n, a j * Real.sin (α j)) := by 
    have h7 : ∀ j : Fin n, a j * (Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1) =
      Real.cos 1 * (a j * Real.cos (α j)) - Real.sin 1 * (a j * Real.sin (α j)) := by 
      intro j
      ring
    have h8 : ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos 1 - Real.sin (α j) * Real.sin 1) = ∑ j : Fin n, (Real.cos 1 * (a j * Real.cos (α j)) - Real.sin 1 * (a j * Real.sin (α j))) := by 
      apply Finset.sum_congr
      · rfl 
      · intro j _
        exact h7 j 
    rw [h8]
    rw [Finset.sum_sub_distrib]
    congr
    · rw [← Finset.mul_sum]
    · rw [← Finset.mul_sum]
  rw [eq3] at h₁ 
  rw [h₀] at h₁ 
  have hsin : ∑ j : Fin n, a j * Real.sin (α j) = 0 := by
    have h4 : Real.sin 1 ≠ 0 := by 
      have h5 : Real.sin 1 > 0 := by 
        apply Real.sin_pos_of_pos_of_lt_pi 
        all_goals linarith [Real.pi_gt_three]
      linarith 
    apply (mul_left_inj' h4).mp 
    linarith 
  have eq6 : ∑ j : Fin n, a j * Real.cos (α j + Real.pi / 10) = ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos (Real.pi / 10) - Real.sin (α j) * Real.sin (Real.pi / 10)) := by 
    apply Finset.sum_congr
    · rfl
    · intro j _
      have eq7 : Real.cos (α j + Real.pi / 10) = Real.cos (α j) * Real.cos (Real.pi / 10) - Real.sin (α j) * Real.sin (Real.pi / 10) := by 
        rw [Real.cos_add]
      rw [eq7]
      all_goals ring 
  have eq8 : ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos (Real.pi / 10) - Real.sin (α j) * Real.sin (Real.pi / 10)) =
    Real.cos (Real.pi / 10) * (∑ j : Fin n, a j * Real.cos (α j)) - Real.sin (Real.pi / 10) * (∑ j : Fin n, a j * Real.sin (α j)) := by 
    have h7 : ∀ j : Fin n, a j * (Real.cos (α j) * Real.cos (Real.pi / 10) - Real.sin (α j) * Real.sin (Real.pi / 10)) =
      Real.cos (Real.pi / 10) * (a j * Real.cos (α j)) - Real.sin (Real.pi / 10) * (a j * Real.sin (α j)) := by 
      intro j 
      ring 
    have h8 : ∑ j : Fin n, a j * (Real.cos (α j) * Real.cos (Real.pi / 10) - Real.sin (α j) * Real.sin (Real.pi / 10)) = ∑ j : Fin n, (Real.cos (Real.pi / 10) * (a j * Real.cos (α j)) - Real.sin (Real.pi / 10) * (a j * Real.sin (α j))) := by 
      apply Finset.sum_congr 
      · rfl
      · intro j _
        exact h7 j 
    rw [h8]
    rw [Finset.sum_sub_distrib]
    congr
    · rw [← Finset.mul_sum]
    · rw [← Finset.mul_sum]
  rw [eq6]
  rw [eq8]
  rw [h₀, hsin]
  all_goals norm_num