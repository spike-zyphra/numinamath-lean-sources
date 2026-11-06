import Mathlib

theorem algebra_173226 {a b c : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h1 : (-a + b + c) / a = (a - b + c) / b) (h2 : (a - b + c) / b = (a + b - c) / c) :
    ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 ∨ ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 := by
  have eq1 : b * (-a + b + c) = a * (a - b + c) := by 
    have h1' : a ≠ 0 := h
    have h2' : b ≠ 0 := h'
    field_simp [h1', h2'] at h1 ⊢
    linarith
  have eq2 : c * (a - b + c) = b * (a + b - c) := by 
    have h1' : b ≠ 0 := h'
    have h2' : c ≠ 0 := h''
    field_simp [h1', h2'] at h2 ⊢
    linarith
  have eq3 : (a - b) * (a + b + c) = 0 := by 
    linarith [eq1]
  have eq4 : (c - b) * (a + b + c) = 0 := by 
    linarith [eq2]
  by_cases h3 : a + b + c = 0
  · -- Case where a + b + c = 0
    have h4 : (a + b) * (b + c) * (c + a) = - (a * b * c) := by
      have h5 : a + b = -c := by linarith
      have h6 : b + c = -a := by linarith
      have h7 : c + a = -b := by linarith
      calc
        (a + b) * (b + c) * (c + a) = (-c) * (-a) * (-b) := by 
          rw [h5, h6, h7]
        _ = - (a * b * c) := by 
          ring
    have eq5 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by
      have eq6 : (a * b * c) ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact h
        exact h'
        exact h''
      have eq7 : (a + b) * (b + c) * (c + a) = - (a * b * c) := h4
      have eq8 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = (- (a * b * c)) / (a * b * c) := by 
        rw [eq7]
      have eq9 : (- (a * b * c)) / (a * b * c) = -1 := by 
        have h1 : a * b * c ≠ 0 := eq6
        field_simp [h1]
      rw [eq8, eq9]
    left
    exact eq5
  · -- Case where a + b + c ≠ 0
    have h4 : a - b = 0 := by
      cases (mul_eq_zero.mp eq3) with
      | inl h4 => 
        linarith
      | inr h4 => 
        exfalso
        apply h3
        linarith
    have eq5 : c - b = 0 := by
      cases (mul_eq_zero.mp eq4) with
      | inl h5 => 
        linarith
      | inr h5 => 
        exfalso
        apply h3
        linarith
    have eq6 : a = b := by linarith
    have eq7 : c = b := by linarith
    have eq9 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by
      rw [show b = a by linarith [eq6]]
      rw [show c = a by linarith [eq6, eq7]]
      ring
    have eq10 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 := by
      have eq11 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := eq9
      have eq12 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact h
        exact h'
        exact h''
      have eq13 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = (8 * (a * b * c)) / (a * b * c) := by 
        rw [eq11]
      have eq14 : (8 * (a * b * c)) / (a * b * c) = 8 := by
        have eq15 : a * b * c ≠ 0 := eq12
        field_simp [eq15]
        <;> nlinarith
      rw [eq13, eq14]
    right
    exact eq10