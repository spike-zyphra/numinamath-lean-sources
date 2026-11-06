import Mathlib

open Polynomial

/- 8. Dato il sistema


$$

\left\{\begin{array}{l}
x+y+z=7 \\
x^{2}+y^{2}+z^{2}=27 \\
x y z=5
\end{array}\right.

$$


quante terne ordinate di numeri reali $(x, y, z)$ ne sono soluzione?
(A) 6
(B) 3
(C) 2
(D) 0
(E) Infinite. -/
theorem algebra_135377 :
    {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = 7 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 27 ∧ x * y * z = 5}.ncard = 3 := by
      -- we'll prove that the only valid solutions are permuations of (1, 1, 5), i.e.
      -- (x, y, z) = (1, 1, 5)
      -- (x, y, z) = (5, 1, 1)
      -- (x, y, z) = (1, 5, 1)
      suffices : {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = 7 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 27 ∧ x * y * z = 5}
        = {(1, 1, 5), (5, 1, 1), (1, 5, 1)}
      · rw [this]
        norm_num

      ext ⟨x, y, z⟩
      -- simplify
      norm_num

      -- we'll prove that the equations imply that (x, y, z) is a permutation of (1, 1, 5),
      -- then we'll show that every solution is valid
      constructor
      -- we have the system of equations
      -- x + y + z = 7
      -- x ^ 2 + y ^ 2 + z ^ 2 = 27
      -- x * y * z = 5
      · intro ⟨aa, bb, cc⟩

        -- we have that
        -- (x + y + z) ^ 2 = 27 + 2 * (x * y + y * z + z * x)
        have s_sq : (x + y + z) ^ 2 = 27 + 2 * (x * y + y * z + z * x) := by
          -- expand square
          trans x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x)
          · ring
          -- simplify using x ^ 2 + y ^ 2 + z ^ 2 = 27
          rw [bb]

        -- then we know that 27 + 2 * (x * y + y * z + z * x)
        have q_eq : x * y + y * z + z * x = 11 := by
          rw [aa] at s_sq
          linarith

        -- consider the polynomial (X - x) * (X - y) * (X - z)
        let P : ℝ[X] := (X - C x) * (X - C y) * (X - C z)

        -- it's roots are x, y and z
        have P_roots : P.roots = {x, y, z} := by
          -- factors are non-zero, so the polynomial is non-zero
          have ne_zerox : (X - C x) ≠ 0 := X_sub_C_ne_zero x
          have ne_zeroy : (X - C y) ≠ 0 := X_sub_C_ne_zero y
          have ne_zeroz : (X - C z) ≠ 0 := X_sub_C_ne_zero z
          have prod_ne : (X - C x) * (X - C y) ≠ 0
            := (mul_ne_zero_iff_right ne_zeroy).mpr ne_zerox
          have prod_ne' : (X - C x) * (X - C y) * (X - C z) ≠ 0
            := (mul_ne_zero_iff_right ne_zeroz).mpr prod_ne

          -- roots of products are union of roots
          norm_num [Polynomial.roots_mul prod_ne', Polynomial.roots_mul prod_ne]

        -- but the polynomial is also equal to X ^ 3 - 7 * X ^ 2 + 11 * X - 5
        have P_eq : P = X ^ 3 - C 7 * X ^ 2 + C 11 * X - C 5 := by
          -- expand P
          trans X ^ 3 - C (x + y + z) * X ^ 2 + C (x * y + y * z + z * x) * X - C (x * y * z)
          · apply Polynomial.funext
            intro t
            norm_num [P]
            ring_nf
          -- we have expressions for each coefficient
          rw [q_eq, cc, aa]

        -- 1 is a root of the polynomial
        have one_mem : 1 ∈ P.roots := by
          rw [P_eq]
          norm_num
          -- it's non-zero
          · apply_fun (coeff · 0)
            norm_num

        -- 5 is a root of the polynomial
        have five_mem : 5 ∈ P.roots := by
          rw [P_eq]
          norm_num
          -- it's non-zero
          · apply_fun (coeff · 0)
            norm_num

        -- so one of x y z is equal to 5
        have five_cases : x = 5 ∨ y = 5 ∨ z = 5 := by
          rw [P_roots] at five_mem
          norm_num at five_mem
          tauto

        -- and one of x y z is equal to 1
        have one_cases : x = 1 ∨ y = 1 ∨ z = 1 := by
          rw [P_roots] at one_mem
          norm_num at one_mem
          tauto

        -- considering every case, the remaining variable must be equal to 1 (because x * y * z = 5), so we have our solutions
        rcases five_cases with rfl | rfl | rfl
        all_goals
        · norm_num at one_cases
          rcases one_cases with rfl | rfl
          all_goals
          · norm_num
            linarith
      -- the solution are valid
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num