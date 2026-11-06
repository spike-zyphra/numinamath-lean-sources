import Mathlib

theorem algebra_68224 {a b c d k : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h1 : a * k ^ 3 + b * k ^ 2 + c * k + d = 0) (h2 : b * k ^ 3 + c * k ^ 2 + d * k + a = 0) :
    k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I := by
  have eq1 : a * k ^ 4 + b * k ^ 3 + c * k ^ 2 + d * k = 0 := by
    calc
      a * k ^ 4 + b * k ^ 3 + c * k ^ 2 + d * k = k * (a * k ^ 3 + b * k ^ 2 + c * k + d) := by ring
      _ = k * 0 := by rw [h1]
      _ = 0 := by simp

  have eq2 : a * k ^ 4 - a = 0 := by
    calc
      a * k ^ 4 - a = (a * k ^ 4 + b * k ^ 3 + c * k ^ 2 + d * k) - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by
        ring_nf
      _ = 0 - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by rw [eq1]
      _ = - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring
      _ = - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring
      _ = -0 := by rw [h2]
      _ = (0 : ℂ) := by simp
  -- Now we can conclude $k^4 - 1 = 0$ since $a \neq 0$
  have h3 : a * (k ^ 4 - 1) = 0 := by
    calc
      a * (k ^ 4 - 1) = (a * k ^ 4 - a) := by ring
      _ = 0 := eq2

  have hk4 : k ^ 4 - 1 = 0 := by
    apply_fun (λ z => z / a) at h3
    field_simp [ha] at h3
    exact h3
  
  have hk1 : k ^ 4 = 1 := by 
    calc 
      k ^ 4 = (k ^ 4 - 1) + 1 := by ring
      _ = 0 + 1 := by rw [hk4]
      _ = 1 := by simp

  -- Solving k^4 = 1, which means that k is a 4th root of unity
  have h4 : k ^ 4 = 1 := hk1
  
  -- Factorizing k^4 - 1 = 0 into linear factors 
  have h7 : k ^ 4 - 1 = (k - 1) * (k + 1) * (k - Complex.I) * (k + Complex.I) := by
    ring_nf
    <;> simp [Complex.I_mul_I]
    <;> ring
  
  -- Apply the factorization to conclude that one of the factors must be zero 
  rw [h7] at hk4 
  cases' (mul_eq_zero.mp hk4) with hk1 hk2 
  cases' (mul_eq_zero.mp hk1) with hk3 hk4 
  cases' (mul_eq_zero.mp hk3) with hk5 hk6 
  · -- hk5: k - 1 = 0 → k = 1
    have hk1 : k = 1 := by 
      exact eq_of_sub_eq_zero hk5
    left 
    exact hk1
  · -- hk6: k + 1 = 0 → k = -1
    have hk2 : k = -1 := by 
      exact eq_neg_of_add_eq_zero_left hk6
    right 
    left 
    exact hk2
  · -- hk4: k - i = 0 → k = i
    have hk3 : k = Complex.I := by 
      exact eq_of_sub_eq_zero hk4
    right 
    right 
    left 
    exact hk3
  · -- hk2: k + i = 0 → k = -i
    have hk4 : k = -Complex.I := by 
      exact eq_neg_of_add_eq_zero_left hk2
    right 
    right 
    right 
    exact hk4