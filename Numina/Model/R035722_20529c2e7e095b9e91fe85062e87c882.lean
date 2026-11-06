import Mathlib

theorem algebra_251471 (m n p a b c : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : m / a = n / b ∧ n / b = p / c) :
    Real.sqrt (m * a) + Real.sqrt (n * b) + Real.sqrt (p * c) =
    Real.sqrt ((m + n + p) * (a + b + c)) := by

  have h1 : m / a = n / b := h.1
  have h2 : n / b = p / c := h.2

  have h3 : m * b = n * a := by
    have hne1 : a ≠ 0 := by linarith
    have hne2 : b ≠ 0 := by linarith
    field_simp [hne1, hne2] at h1 ⊢
    linarith

  have h4 : n * c = p * b := by
    have hne1 : b ≠ 0 := by linarith
    have hne2 : c ≠ 0 := by linarith
    field_simp [hne1, hne2] at h2 ⊢
    linarith

  have eq1 : m = (n * a) / b := by
    field_simp [(show b ≠ 0 by linarith)] at h3 ⊢
    linarith

  have eq2 : p = (n * c) / b := by
    field_simp [(show b ≠ 0 by linarith)] at h4 ⊢
    linarith

  have eq3 : Real.sqrt (m * a) = a * Real.sqrt (n / b) := by
    rw [eq1]
    have h5 : ((n * a) / b) * a = (n / b) * (a ^ 2) := by
      field_simp [(show b ≠ 0 by linarith)]
      <;> ring
    rw [h5]
    have h6 : Real.sqrt ((n / b) * (a ^ 2)) = Real.sqrt (n / b) * Real.sqrt (a ^ 2) := by
      rw [Real.sqrt_mul (by 
        have : 0 ≤ n / b := by positivity
        linarith
      )]
    rw [h6]
    have h7 : Real.sqrt (a ^ 2) = a := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h7]
    all_goals nlinarith [Real.sqrt_nonneg (n / b), Real.sqrt_nonneg ((n / b) * (a ^ 2)), Real.sqrt_nonneg (a ^ 2)]

  have eq4 : Real.sqrt (p * c) = c * Real.sqrt (n / b) := by
    rw [eq2]
    have h5 : ((n * c) / b) * c = (n / b) * (c ^ 2) := by
      field_simp [(show b ≠ 0 by linarith)]
      <;> ring
    rw [h5]
    have h6 : Real.sqrt ((n / b) * (c ^ 2)) = Real.sqrt (n / b) * Real.sqrt (c ^ 2) := by
      rw [Real.sqrt_mul (by 
        have : 0 ≤ n / b := by positivity
        linarith
      )]
    rw [h6]
    have h7 : Real.sqrt (c ^ 2) = c := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h7]
    all_goals nlinarith [Real.sqrt_nonneg (n / b), Real.sqrt_nonneg ((n / b) * (c ^ 2)), Real.sqrt_nonneg (c ^ 2)]

  have eq5 : Real.sqrt ((m + n + p) * (a + b + c)) = Real.sqrt (n / b) * (a + b + c) := by
    have h7 : (m + n + p) * (a + b + c) = (n / b) * ((a + b + c) ^ 2) := by
      have h8 : m + n + p = (n / b) * (a + b + c) := by
        have h9 : m = (n * a) / b := by linarith [eq1]
        have h10 : p = (n * c) / b := by linarith [eq2]
        rw [h9, h10]
        field_simp [(show b ≠ 0 by linarith)]
        <;> ring
      rw [h8]
      <;> field_simp [(show b ≠ 0 by linarith)] at *
      <;> ring_nf <;> norm_num
    rw [h7]
    have h8 : Real.sqrt ((n / b) * ((a + b + c) ^ 2)) = Real.sqrt (n / b) * Real.sqrt ((a + b + c) ^ 2) := by
      rw [Real.sqrt_mul (by
        have : 0 ≤ n / b := by positivity
        linarith
      )]
    rw [h8]
    have h9 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq (by positivity)]
    rw [h9]
    all_goals ring_nf <;> norm_num
    all_goals nlinarith
  have eq7 : Real.sqrt (n * b) = Real.sqrt (n / b) * b := by
    have h11 : Real.sqrt (n * b) = Real.sqrt ((n / b) * (b ^ 2)) := by
      field_simp [(show b ≠ 0 by linarith)]
      <;> ring_nf <;> field_simp [(show b ≠ 0 by linarith)]
      all_goals nlinarith
    rw [h11]
    have h12 : Real.sqrt ((n / b) * (b ^ 2)) = Real.sqrt (n / b) * Real.sqrt (b ^ 2) := by
      rw [Real.sqrt_mul (by
        have : 0 ≤ n / b := by positivity
        linarith
      )]
    rw [h12]
    have h13 : Real.sqrt (b ^ 2) = b := by
      rw [Real.sqrt_sq (by linarith)]
    rw [h13]
    all_goals ring_nf <;> norm_num
    all_goals nlinarith
  rw [eq3, eq4, eq5, eq7]
  all_goals ring_nf <;> norm_num
  all_goals nlinarith [Real.sqrt_nonneg (n / b), Real.sqrt_nonneg (a ^ 2), Real.sqrt_nonneg (c ^ 2), Real.sqrt_nonneg (b ^ 2)]