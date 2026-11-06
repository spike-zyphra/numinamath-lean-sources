import Mathlib

open scoped EuclideanGeometry

/- The graph of $y=x^2+2x-15$ intersects the $x$-axis at points $A$ and $C$ and the $y$-axis at point $B$. What is $\tan(\angle ABC)$?
$\textbf{(A)}\ \frac{1}{7} \qquad \textbf{(B)}\ \frac{1}{4} \qquad \textbf{(C)}\ \frac{3}{7} \qquad \textbf{(D)}\ \frac{1}{2} \qquad \textbf{(E)}\ \frac{4}{7} \qquad$ -/
theorem algebra_95346 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 2 * x - 15)
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hA : A 1 = 0)
    (hB : B 0 = 0)
    (hC : C 1 = 0)
    (hfA : f (A 0) = 0)
    (hfB : f 0 = B 1)
    (hfC : f (C 0) = 0)
    (hAC : A 0 < C 0) :
    Real.tan (∠ A B C) = 4 / 7 := by

    -- We calculate the coordinates of the points A, B and C
    -- First we have f 0 = B 1 = -15
    have hB1 : B 1 = -15 := by simp [hf] at hfB; exact hfB.symm

    -- We solve the quadratic equation f x = 0 to get the points A and C
    have hf0_rw : ∀ x, f x = 1 * (x * x) + 2 * x + (-15) := by
        intro x
        simp [hf,pow_two]
        rfl

    have hf0 : ∀ x, f x = 0 → x = 3 ∨ x = -5 := by
        intro x hx
        have h0 := hf0_rw x
        rw [hx] at h0
        have h_discrim : discrim (1:ℝ) 2 (-15) = 8 * 8 := by simp [discrim]; norm_num
        have hf0_aux := (quadratic_eq_zero_iff (by norm_num) h_discrim x).1 h0.symm
        norm_num at hf0_aux
        exact hf0_aux

    -- We separate the cases for the points A and C
    have h_diff (x y : ℝ) (hxy : x < y) (hx : x = 3 ∨ x = -5) (hy : y = 3 ∨ y = -5) : x = -5 ∧ y = 3 := by
        cases hx with
        |   inl hx3 =>
                cases hy with
                |   inl hy3 => linarith
                |   inr hy_5 => linarith
        |   inr hx_5 =>
                cases hy with
                |   inl hy3 => exact ⟨hx_5, hy3⟩
                |   inr hy_5 => linarith

    have hA0 : A 0 = -5 := (h_diff (A 0) (C 0) hAC (hf0 _ hfA) (hf0 _ hfC)).1
    have hC0 : C 0 = 3 := (h_diff (A 0) (C 0) hAC (hf0 _ hfA) (hf0 _ hfC)).2

    have hPtoRepr (P : EuclideanSpace ℝ (Fin 2)) : P = ![P 0, P 1] := by ext i; fin_cases i <;> simp

    have hA_sol : A = ![-5, 0] := by rw [←hA0,←hA]; exact hPtoRepr A
    have hB_sol : B = ![0, -15] := by rw [←hB1,←hB]; exact hPtoRepr B
    have hC_sol : C = ![3, 0] := by rw [←hC0,←hC]; exact hPtoRepr C

    -- Now we have the coordinates of the points A, B and C, so we can calculate the angle
    simp [hA_sol, hB_sol, hC_sol]

    -- Use the formula ∠ A B C = arccos ((AB • BC) / (||AB|| * ||BC||))
    simp [EuclideanGeometry.angle, InnerProductGeometry.angle]

    -- Then we reduce and calculate
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    rw [←Real.sqrt_mul]
    norm_num
    have h49 : (49:ℝ) = 7 * 7 := by norm_num
    rw [←Real.sqrt_mul_self (x:=210),←Real.sqrt_div']
    norm_num
    simp [h49]

    -- We use the formula tan (arccos x) = sqrt (1 - x ^ 2) / x
    simp [Real.tan_arccos,pow_two]
    ring_nf
    simp
    norm_num
    have h16 : (16:ℝ) = 4 * 4 := by norm_num
    simp [h16]
    ring

    -- We resolve the remaining positivity conditions for the square roots
    norm_num
    norm_num
    norm_num