import Mathlib

theorem algebra_247167 (x y : ℤ) :
    y^4 - x * (x + 1) * (x + 2) * (x + 3) = 1 ↔
    (x, y) = (0, -1) ∨ (x, y) = (0, 1) ∨ (x, y) = (-3, 1) ∨ (x, y) = (-3, -1) ∨
    (x, y) = (-1, 1) ∨ (x, y) = (-1, -1) ∨ (x, y) = (-2, 1) ∨ (x, y) = (-2, -1) := by
  constructor
  · -- Forward: if $(x,y)$ satisfies the equation, then it's one of the given solutions.
    rintro h_eq
    have h1 : y^4 = x * (x + 1) * (x + 2) * (x + 3) + 1 := by 
      linarith
    have h2 : x * (x + 1) * (x + 2) * (x + 3) + 1 = (x^2 + 3 * x + 1)^2 := by
      ring
    have h3 : y^4 = (x^2 + 3 * x + 1)^2 := by 
      rw [h2] at h1 
      linarith
    have h4 : y^2 = x^2 + 3 * x + 1 ∨ y^2 = - (x^2 + 3 * x + 1) := by 
      have h5 : (y ^ 2) ^ 2 = (x^2 + 3 * x + 1) ^ 2 := by 
        nlinarith [h3]
      have h6 : (y ^ 2 - (x^2 + 3 * x + 1)) * (y ^ 2 + (x^2 + 3 * x + 1)) = 0 := by 
        nlinarith [h5]
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- The first factor is zero: $y^2 - (x^2 +3 *x +1)=0$.
        left 
        linarith
      · -- The second factor is zero: $y^2 + (x^2 +3 *x +1)=0$.
        right 
        linarith
    rcases h4 with h7 | h7
    · -- Case $y^2 = x^2 + 3 * x + 1$.
      have h5 : 4 * y^2 = 4 * x^2 + 12 * x + 4 := by 
        nlinarith [h7]
      have h6 : 4 * y^2 = (2 * x + 3) ^ 2 - 5 := by
        nlinarith [h5]
      have h7 : (2 * y - (2 * x + 3)) * (2 * y + (2 * x + 3)) = -5 := by
        nlinarith [h6]
      have h8 : (2 * y - (2 * x + 3)) ∣ -5 := by
        use (2 * y + (2 * x + 3))
        linarith [h7]
      have h9 : (2 * y - (2 * x + 3)) ∣ 5 := by
        exact Int.dvd_neg.mp h8
      have h10 : (2 * y - (2 * x + 3)) ∣ 5 := h9
      have h11 : (2 * y - (2 * x + 3)) ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h10
      have h12 : (2 * y - (2 * x + 3)) ≥ -5 := by
        have h40 : (- (2 * y - (2 * x + 3)) ) ∣ 5 := by 
          exact Int.neg_dvd.2 h10
        have h41 : - (2 * y - (2 * x + 3)) ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h40 
        omega
      interval_cases h : (2 * y - (2 * x + 3)) <;> norm_num at h7 ⊢ 
      <;> norm_num [Prod.ext_iff] at *
      <;> omega
    · -- Case $y^2 = - (x^2 + 3 * x +1)$.
      have h0 : y^2 = - (x^2 + 3 * x + 1) := h7
      have h00 : x^2 + 3 * x + 1 ≤ 0 := by
        nlinarith [show y^2 ≥ 0 by nlinarith, h0]
      have h11 : x ≥ -2 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (y), sq_nonneg (y - 1), sq_nonneg (y + 1)]
      have h12 : x ≤ -1 := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (y), sq_nonneg (y - 1), sq_nonneg (y + 1)]
      interval_cases x <;> try { 
        have h2 : y ≤ 1 := by nlinarith [sq_nonneg (y^2), h0]
        have h3 : y ≥ -1 := by nlinarith [sq_nonneg (y^2), h0]
        interval_cases y <;> norm_num [Prod.ext_iff] at *
        <;> omega
      }
  · -- Backward: if $(x,y)$ is one of the given solutions, then it satisfies the equation.
    rintro (h | h | h | h | h | h | h | h)
    · -- Check (0, -1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (0, 1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-3, 1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-3, -1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-1, 1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-1, -1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-2, 1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- Check (-2, -1)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num