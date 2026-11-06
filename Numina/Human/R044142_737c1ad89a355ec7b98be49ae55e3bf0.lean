import Mathlib

/- Solve the following system of equations in integer numbers: $\begin{cases}x^{2}=yz+1\\y^{2}=zx+1\\z^{2}=xy+1\end{cases}$ -/
theorem number_theory_73551 {x y z : ℤ} (h1 : x ^ 2 = y * z + 1) (h2 : y ^ 2 = z * x + 1)
    (h3 : z ^ 2 = x * y + 1) :
    (x, y, z) = (1, 0, -1) ∨ (x, y, z) = (-1, 0, 1) ∨ (x, y, z) = (0, 1, -1) ∨
    (x, y, z) = (0, -1, 1) ∨ (x, y, z) = (-1, 1, 0) ∨ (x, y, z) = (1, -1, 0) := by 
  have h4 : (x - y) * (x + y + z) = 0 := by 
    nlinarith [h1, h2]
  cases (mul_eq_zero.mp h4) with
  | inl hxy =>
    have h_eq : x = y := by linarith
    have h5 : z^2 = x^2 + 1 := by 
      nlinarith [h3, h_eq]
    have h6 : (z - x) * (z + x) = 1 := by 
      nlinarith [h5]
    have h7 : z - x = 1 ∨ z - x = -1 := by 
      have h : (z - x) * (z + x) = 1 := h6
      have h8 : z - x = 1 ∨ z - x = -1 := by
        have h9 : (z - x) = 1 ∨ (z - x) = -1 := by 
          have h10 : (z - x) * (z + x) = 1 := h
          apply Int.eq_one_or_neg_one_of_mul_eq_one
          exact h10
        exact h9
      exact h8
    cases h7 with
    | inl hz1 =>
      have h9 : z + x = 1 := by 
        nlinarith [hz1, h6]
      have h10 : x = 0 := by 
        have h11 : z + x = 1 := h9
        have h12 : z - x = 1 := hz1
        linarith
      have h11 : y = 0 := by linarith [h_eq, h10]
      have h12 : z = 1 := by linarith [h9, h10]
      rw [h10, h11, h12] at h1
      all_goals omega
    | inr hz2 =>
      have h9 : z + x = -1 := by 
        nlinarith [hz2, h6]
      have h10 : x = 0 := by 
        have h11 : z + x = -1 := h9
        have h12 : z - x = -1 := hz2
        linarith
      have h11 : y = 0 := by linarith [h_eq, h10]
      have h12 : z = -1 := by linarith [h9, h10]
      rw [h10, h11, h12] at h1
      all_goals omega
  | inr h_sum =>
    have hz : z = -x - y := by linarith
    have h_eq : x^2 + x * y + y^2 = 1 := by 
      rw [hz] at h1
      nlinarith
    have hx : x = -1 ∨ x = 0 ∨ x = 1 := by 
      have h1 : x ≤ 1 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), h_eq]
      have h2 : x ≥ -1 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), h_eq]
      omega
    have hy : y = -1 ∨ y = 0 ∨ y = 1 := by 
      have h1 : y ≤ 1 := by 
        nlinarith [sq_nonneg (y - 1), sq_nonneg (x), sq_nonneg (x - y), sq_nonneg (x + y), h_eq]
      have h2 : y ≥ -1 := by 
        nlinarith [sq_nonneg (y + 1), sq_nonneg (x), sq_nonneg (x - y), sq_nonneg (x + y), h_eq]
      omega
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> 
    ( 
      simp [hx, hy] at h_eq <;> 
      try { 
        simp [hx, hy, hz]
      }
    )