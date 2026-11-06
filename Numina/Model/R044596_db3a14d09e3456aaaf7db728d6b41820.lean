import Mathlib

theorem algebra_327977 (x y z a b c : ℝ) (d1 : y+z ≠ 0) (d2 : z+x ≠ 0) (d3: x+y ≠ 0)
(h₀ : x + y + z ≠ 0) 
(h₁ : x / (y + z) = a)
(h₂ : y / (z + x) = b) (h₃ : z / (x + y) = c) :
  (3 * a / (1 + a) ≥ 1 ∨ 3 * b / (1 + b) ≥ 1 ∨ 3 * c / (1 + c) ≥ 1) ∧
  (3 * a / (1 + a) ≤ 1 ∨ 3 * b / (1 + b) ≤ 1 ∨ 3 * c / (1 + c) ≤ 1) := by

  have h4 : 1 + a ≠ 0 := by 
    by_contra h
    have ha1 : a = -1 := by linarith 
    rw [ha1] at h₁ 
    have h₁₁ : x = -y - z := by 
      field_simp [d1] at h₁
      linarith 
    have eq1 : x + y + z = 0 := by
      linarith [h₁₁]
    exfalso 
    exact h₀ eq1 
  have h5 : 1 + b ≠ 0 := by 
    by_contra h
    have hb1 : b = -1 := by linarith 
    rw [hb1] at h₂ 
    have h₂₂ : y = -x - z := by 
      field_simp [d2] at h₂
      linarith 
    have eq1 : x + y + z = 0 := by 
      linarith [h₂₂]
    exfalso 
    exact h₀ eq1 
  have h6 : 1 + c ≠ 0 := by 
    by_contra h
    have hc1 : c = -1 := by linarith 
    rw [hc1] at h₃ 
    have h₃₃ : z = -x - y := by 
      field_simp [d3] at h₃ 
      linarith 
    have eq1 : x + y + z = 0 := by 
      linarith [h₃₃]
    exfalso 
    exact h₀ eq1 
  have h7 : 3 * a / (1 + a) = 3 * x / (x + y + z) := by
    have ha1 : a = x / (y + z) := by 
      linarith [h₁] 
    rw [ha1] 
    have h8 : 1 + x / (y + z) = (x + y + z) / (y + z) := by 
      field_simp [d1]
      <;> ring 
    rw [h8]
    <;> field_simp [h₀, d1]
    <;> ring 
  have h8 : 3 * b / (1 + b) = 3 * y / (x + y + z) := by
    have hb1 : b = y / (z + x) := by 
      linarith [h₂] 
    rw [hb1] 
    have h9 : 1 + y / (z + x) = (x + y + z) / (z + x) := by 
      field_simp [d2]
      <;> ring 
    rw [h9]
    <;> field_simp [h₀, d2]
    <;> ring 
  have h9 : 3 * c / (1 + c) = 3 * z / (x + y + z) := by 
    have hc1 : c = z / (x + y) := by 
      linarith [h₃] 
    rw [hc1] 
    have h10 : 1 + z / (x + y) = (x + y + z) / (x + y) := by 
      field_simp [d3]
      <;> ring 
    rw [h10]
    <;> field_simp [h₀, d3]
    <;> ring 
  constructor 
  · -- Prove that at least one is not less than 1
    by_contra h
    push_neg at h
    have h10 : 3 * x / (x + y + z) < 1 := by 
      have h11 : 3 * a / (1 + a) < 1 := by
        tauto 
      rw [h7] at h11 
      linarith 
    have h11 : 3 * y / (x + y + z) < 1 := by 
      have h12 : 3 * b / (1 + b) < 1 := by
        tauto 
      rw [h8] at h12 
      linarith 
    have h12 : 3 * z / (x + y + z) < 1 := by 
      have h13 : 3 * c / (1 + c) < 1 := by
        tauto 
      rw [h9] at h13 
      linarith 
    by_cases h : x + y + z > 0
    · -- assume x + y + z > 0
      have h14 : 3 * x < (x + y + z) := by
        have h100 : 3 * x / (x + y + z) < 1 := h10 
        apply (div_lt_iff₀ (by linarith)).mp at h100 
        linarith 
      have h15 : 3 * y < (x + y + z) := by
        have h110 : 3 * y / (x + y + z) < 1 := h11 
        apply (div_lt_iff₀ (by linarith)).mp at h110 
        linarith 
      have h16 : 3 * z < (x + y + z) := by
        have h120 : 3 * z / (x + y + z) < 1 := h12 
        apply (div_lt_iff₀ (by linarith)).mp at h120 
        linarith 
      nlinarith 
    · -- x + y + z ≤ 0
      have hx2 : x + y + z ≤ 0 := by
        by_contra h
        push_neg at h
        have h10' : x + y + z > 0 := by linarith 
        nlinarith 
      by_cases h9 : x + y + z < 0 
      · -- Assume x + y + z < 0
        have hx2 : x + y + z < 0 := h9
        have h14 : 3 * x > (x + y + z) := by
          have h100 : 3 * x / (x + y + z) < 1 := h10 
          apply (div_lt_iff_of_neg' (by linarith)).mp at h100 
          linarith 
        have h15 : 3 * y > (x + y + z) := by
          have h110 : 3 * y / (x + y + z) < 1 := h11 
          apply (div_lt_iff_of_neg' (by linarith)).mp at h110 
          linarith 
        have h16 : 3 * z > (x + y + z) := by
          have h120 : 3 * z / (x + y + z) < 1 := h12 
          apply (div_lt_iff_of_neg' (by linarith)).mp at h120 
          linarith 
        nlinarith 
      · -- x + y + z ≥ 0
        have hx3 : x + y + z = 0 := by 
          linarith 
        contradiction 
  · -- Prove that at least one is not greater than 1
    by_contra h
    push_neg at h
    have h10 : 3 * x / (x + y + z) > 1 := by 
      have h11 : 3 * a / (1 + a) > 1 := by
        tauto 
      rw [h7] at h11 
      linarith 
    have h11 : 3 * y / (x + y + z) > 1 := by 
      have h12 : 3 * b / (1 + b) > 1 := by
        tauto 
      rw [h8] at h12 
      linarith 
    have h12 : 3 * z / (x + y + z) > 1 := by 
      have h13 : 3 * c / (1 + c) > 1 := by
        tauto 
      rw [h9] at h13 
      linarith 
    by_cases h : x + y + z > 0
    · -- assume x + y + z > 0
      have h14 : 3 * x > (x + y + z) := by
        have h100 : 3 * x / (x + y + z) > 1 := h10 
        apply (lt_div_iff₀ (by linarith)).mp at h100 
        linarith 
      have h15 : 3 * y > (x + y + z) := by
        have h110 : 3 * y / (x + y + z) > 1 := h11 
        apply (lt_div_iff₀ (by linarith)).mp at h110 
        linarith 
      have h16 : 3 * z > (x + y + z) := by
        have h120 : 3 * z / (x + y + z) > 1 := h12 
        apply (lt_div_iff₀ (by linarith)).mp at h120 
        linarith 
      nlinarith 
    · -- x + y + z ≤ 0
      have hx2 : x + y + z ≤ 0 := by
        by_contra h
        push_neg at h
        have h10' : x + y + z > 0 := by linarith 
        nlinarith 
      by_cases h9 : x + y + z < 0 
      · -- Assume x + y + z < 0
        have hx2 : x + y + z < 0 := h9
        have h14 : 3 * x < (x + y + z) := by
          have h100 : 3 * x / (x + y + z) > 1 := h10 
          apply (lt_div_iff_of_neg' (by linarith)).mp at h100 
          linarith 
        have h15 : 3 * y < (x + y + z) := by
          have h110 : 3 * y / (x + y + z) > 1 := h11 
          apply (lt_div_iff_of_neg' (by linarith)).mp at h110 
          linarith 
        have h16 : 3 * z < (x + y + z) := by
          have h120 : 3 * z / (x + y + z) > 1 := h12 
          apply (lt_div_iff_of_neg' (by linarith)).mp at h120 
          linarith 
        nlinarith 
      · -- x + y + z ≥ 0
        have hx3 : x + y + z = 0 := by 
          linarith 
        contradiction