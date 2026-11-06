import Mathlib

theorem algebra_322949 (f : ℝ → ℝ) (hf : f = fun x => (x + 12) / (2 * x - 1)) :
    {(x, y) : ℤ × ℤ | y = f x}.ncard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | y = f x} = {(-12, 0), (0, -12), (1, 13), (3, 3), (-2, -2), (13, 1)} := by
    ext ⟨x, y⟩
    simp [hf]
    constructor
    · -- Forward: if $y = f(x)$, then $(x,y)$ is in the set.
      rintro H
      have h3 : y * (2 * x - 1) = x + 12 := by
        have h_eq : (y : ℝ) * (2 * (x : ℝ) - 1) = ((x + 12) : ℝ) := by
          field_simp [(show (2 * (x : ℝ) - 1) ≠ 0 by
            by_contra h'
            have h_eq1 : (2 * (x : ℝ) - 1) = 0 := by linarith
            have h_eq2 : (2 * (x : ℝ)) = (1 : ℝ) := by linarith
            have h_eq3 : 2 * x = 1 := by
              exact_mod_cast h_eq2
            omega
          )] at H ⊢
          nlinarith
        norm_cast at h_eq ⊢
      have h5 : (2 * x - 1) ∣ x + 12 := by
        use y
        all_goals linarith
      have h7 : (2 * x - 1) ∣ 25 := by
        have h19 : (2 * x - 1) ∣ x + 12 := h5
        have h20 : (2 * x - 1) ∣ 2 * (x + 12) := by
          exact dvd_trans h19 (by simp)
        have h21 : (2 * x - 1) ∣ (2 * x - 1) := by
          use 1
          all_goals ring_nf
        have h22 : (2 * x - 1) ∣ 2 * (x + 12) - (2 * x - 1) := by
          apply Dvd.dvd.sub
          · exact h20
          · exact h21
        have h23 : 2 * (x + 12) - (2 * x - 1) = 25 := by
          nlinarith
        rw [h23] at h22
        exact h22

      have h8 : (2 * x - 1) ≤ 25 := by
        apply Int.le_of_dvd (by norm_num) h7
      have h9 : (2 * x - 1) ≥ -25 := by
        have h10 : -(2 * x - 1) ∣ 25 := by
          exact Int.neg_dvd.2 h7
        have h11 : -(2 * x - 1) ≤ 25 := by
          apply Int.le_of_dvd (by norm_num) h10
        omega
      have h10 : x ≤ 13 := by
        omega
      have h11 : x ≥ -12 := by
        omega
      interval_cases x <;> norm_num at h3 h5 h7 ⊢
      <;> omega 
    · -- Backward: if $(x,y)$ is in the set, then $y = f(x)$
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl
        ⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }
  all_goals norm_num