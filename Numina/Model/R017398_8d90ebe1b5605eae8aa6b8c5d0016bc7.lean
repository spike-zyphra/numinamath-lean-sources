import Mathlib

theorem calculus_23024 (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ x y z : ℝ, M * !![x; y; z] = !![y; z; x + y + z]) :
    M = !![0, 1, 0; 0, 0, 1; 1, 1, 1] := by 
  have eq1 := hM 1 0 0
  have eq2 := hM 0 1 0
  have eq3 := hM 0 0 1
  have eq4 := hM 1 1 1
  -- From eq1: M * e1 = e3
  -- From eq2: M * e2 = v2
  -- From eq3: M * e3 = v3
  -- From eq4: M * (1, 1, 1) = (1, 1, 3)
  -- Substituting specific vectors to extract matrix entries
  have eq11 := congr_arg (λ v => v 0 0) eq1
  have eq12 := congr_arg (λ v => v 1 0) eq1
  have eq13 := congr_arg (λ v => v 2 0) eq1
  -- Extract equations for second column
  have eq21 := congr_arg (λ v => v 0 1) eq2
  have eq22 := congr_arg (λ v => v 1 1) eq2
  have eq23 := congr_arg (λ v => v 2 1) eq2
  -- Extract equations for third column
  have eq31 := congr_arg (λ v => v 0 2) eq3
  have eq32 := congr_arg (λ v => v 1 2) eq3
  have eq33 := congr_arg (λ v => v 2 2) eq3
  -- Simplify the equations 
  simp [Matrix.mul_apply, Fin.sum_univ_three] at eq11 eq12 eq13 eq21 eq22 eq23 eq31 eq32 eq33
  -- The equations we get are sufficient to prove that M is the desired matrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eq11, eq12, eq13, eq21, eq22, eq23, eq31, eq32, eq33]