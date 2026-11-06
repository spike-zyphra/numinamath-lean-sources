import Mathlib

theorem calculus_15814 :
    {(a, d) : ℝ × ℝ | ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      A = !![a, 3; -8, d] ∧ A * A = 1}.ncard = 2 := by
  have h1 : {(a, d) : ℝ × ℝ | ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      A = !![a, 3; -8, d] ∧ A * A = 1} = {(-5, 5), (5, -5)} := by
    ext ⟨a, d⟩
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · -- Assume (a, d) in the set.
      rintro ⟨A, hA1, hA2⟩
      rw [hA1] at hA2
      have eq1 := congr_arg (fun X => X 0 0) hA2
      simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two] at eq1
      have eq2 := congr_arg (fun X => X 0 1) hA2
      simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two] at eq2
      have eq3 := congr_arg (fun X => X 1 0) hA2
      simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two] at eq3
      have eq4 := congr_arg (fun X => X 1 1) hA2
      simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two] at eq4
      -- From eq2: 3a + 3d = 0 → a = -d
      have eq5 : d = -a := by
        nlinarith
      have eq6 : a^2 = 25 := by 
        nlinarith 
      have : a = 5 ∨ a = -5 := by 
        have h1 : a^2 = 25 := eq6
        have h2 : a^2 - 25 = 0 := by linarith 
        have h3 : (a - 5) * (a + 5) = 0 := by 
          nlinarith 
        cases (mul_eq_zero.1 h3) with 
        | inl h4 => 
          left 
          linarith 
        | inr h5 => 
          right 
          linarith 
      cases this with
      | inl ha5 =>
        -- case a = 5.
        have had5 : d = -5 := by 
          rw [show a = (5 : ℝ) by linarith [ha5]] at eq5 
          linarith 
        right 
        simp [ha5, had5]
      | inr ha5 =>
        -- case a = -5.
        have had5 : d = 5 := by 
          rw [show a = (-5 : ℝ) by linarith [ha5]] at eq5 
          linarith 
        left 
        simp [ha5, had5]
    · -- Assume (a, d) ∈ {(-5, 5), (5, -5)}
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Case (-5, 5)
        use !![-5, 3; -8, 5]
        all_goals
          simp [Matrix.mul_fin_two, Matrix.of_apply, Matrix.one_fin_two]
          all_goals norm_num
      · -- Case (5, -5)
        use !![5, 3; -8, -5]
        all_goals
          simp [Matrix.mul_fin_two, Matrix.of_apply, Matrix.one_fin_two]
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num