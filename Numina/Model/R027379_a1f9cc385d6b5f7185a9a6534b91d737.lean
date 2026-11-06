import Mathlib

/- Let the line $y=kx+b$ intersect the curve $y=x^3-x$ at three distinct points $A$, $B$, and $C$, and $|AB|=|BC|=2$. Then the value of $k$ is ___          ___. -/
theorem algebra_12142 (k b : ℝ) (h : ∃ A B C : ℝ, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    k * A + b = A ^ 3 - A ∧ k * B + b = B ^ 3 - B ∧ k * C + b = C ^ 3 - C ∧
    Real.sqrt ((B - A) ^ 2 + (k * (B - A)) ^ 2) = 2 ∧
    Real.sqrt ((C - B) ^ 2 + (k * (C - B)) ^ 2) = 2) :
    k = 1 := by
  rcases h with ⟨A, B, C, hab1, hab2, hab3, h1, h2, h3, h4, h5⟩
  have h6 : (B - A) ^ 2 + (k * (B - A)) ^ 2 = 4 := by
    have h6 : Real.sqrt ((B - A) ^ 2 + (k * (B - A)) ^ 2) = 2 := h4
    have h7 : (Real.sqrt ((B - A) ^ 2 + (k * (B - A)) ^ 2)) ^ 2 = 4 := by
      rw [h6]
      norm_num
    have h8 : (Real.sqrt ((B - A) ^ 2 + (k * (B - A)) ^ 2)) ^ 2 = (B - A) ^ 2 + (k * (B - A)) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    linarith
  have h7 : (C - B) ^ 2 + (k * (C - B)) ^ 2 = 4 := by
    have h7 : Real.sqrt ((C - B) ^ 2 + (k * (C - B)) ^ 2) = 2 := h5
    have h8 : (Real.sqrt ((C - B) ^ 2 + (k * (C - B)) ^ 2)) ^ 2 = 4 := by
      rw [h7]
      norm_num
    have h9 : (Real.sqrt ((C - B) ^ 2 + (k * (C - B)) ^ 2)) ^ 2 = (C - B) ^ 2 + (k * (C - B)) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    linarith
  have eq1 : k * (B - A) = (B ^ 3 - B) - (A ^ 3 - A) := by
    linarith
  have eq2 : k * (C - B) = (C ^ 3 - C) - (B ^ 3 - B) := by
    linarith
  have eq3 : k = B ^ 2 + A * B + A ^ 2 - 1 := by
    apply (mul_left_inj' (show B - A ≠ 0 by
      intro h'
      apply hab1
      linarith
    )).mp
    linarith [eq1]
  have eq4 : k = C ^ 2 + B * C + B ^ 2 - 1 := by
    apply (mul_left_inj' (show C - B ≠ 0 by
      intro h'
      apply hab3
      linarith
    )).mp
    linarith [eq2]
  have eq5 : (A - C) * (A + B + C) = 0 := by
    nlinarith [eq3, eq4]
  cases' (mul_eq_zero.mp eq5) with h9 h10
  · -- A - C = 0
    exfalso
    apply hab2
    linarith
  · -- A + B + C = 0
    have hC_subst : C = -A - B := by linarith
    have eq8 : k = A^2 + A * B + B^2 - 1 := by 
      rw [hC_subst] at eq4
      nlinarith
    have eq9 : (-A - 2 * B) ^ 2 = (B - A) ^ 2 := by
      rw [show C = -A - B by linarith [hC_subst]] at h7
      nlinarith [h6, h7, sq_nonneg (B - A), sq_nonneg ((-A - 2 * B))]
    have eq10 : 3 * B * (2 * A + B) = 0 := by
      nlinarith [eq9]
    cases' (mul_eq_zero.mp eq10) with eq11 eq12
    · -- B=0 implies k=1
      have hB0 : B = 0 := by linarith
      have hC0 : C = -A := by 
        rw [hC_subst]
        linarith
      have eq14 : k = A^2 - 1 := by
        rw [hB0] at eq8
        nlinarith
      have h6' : A ^ 2 * (1 + k ^ 2) = 4 := by
        rw [show B = (0 : ℝ) by linarith] at h6
        nlinarith 
      rw [eq14] at h6'
      have ha2_eq_2 : A ^ 2 = 2 := by 
        nlinarith [sq_nonneg (A ^ 2 - 2), sq_nonneg (A), sq_nonneg (A ^ 2)]
      rw [ha2_eq_2] at eq14
      nlinarith
    · -- Case $2A + B = 0 \Rightarrow C = A$ which contradicts with $A \neq C$.
      have hB_eq : B = -2 * A := by linarith
      have hC_eq_A : C = A := by
        rw [hC_subst]
        linarith [hB_eq]
      exfalso 
      apply hab2
      linarith