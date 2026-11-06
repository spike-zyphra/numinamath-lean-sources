import Mathlib

theorem algebra_97991 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(hge : ∃ r:ℝ, r>1 ∧ b = a * r ∧ c = b * r) (hlog : Real.logb 6 a + Real.logb 6 b + Real.logb 6 c = 6)
(hdiff : ∃ m, b - a = m ^ 2) :
a + b + c = 111 := by
  rcases hge with ⟨r, hr1, h1, h2⟩
  rcases hdiff with ⟨m, hm⟩
  have h3 : (a : ℝ) > 0 := by exact_mod_cast ha 
  have h4 : (b : ℝ) > 0 := by exact_mod_cast hb 
  have h5 : (c : ℝ) > 0 := by exact_mod_cast hc
  have h6 : Real.logb 6 a + Real.logb 6 b + Real.logb 6 c = Real.logb 6 (a * b * c) := by
    simp [Real.logb_mul, h3.ne', h4.ne', h5.ne']
  rw [h6] at hlog 
  have h7 : (a * b * c : ℝ) = (6 : ℝ) ^ 6 := by 
    have h8 : Real.logb 6 (a * b * c) = 6 := by 
      linarith 
    have h9 : (a * b * c : ℝ) = (6 : ℝ) ^ (Real.logb 6 (a * b * c)) := by
      field_simp [Real.rpow_logb, show (6 : ℝ) > 1 by norm_num, h3, h4, h5]
    rw [h8] at h9 
    norm_num at h9 ⊢ 
    linarith 
  have eq4 : (a * b * c : ℝ) = (b : ℝ) ^ 3 := by
    have eq5 : (b : ℝ) = (a : ℝ) * r := by
      nlinarith 
    have eq6 : (c : ℝ) = (b : ℝ) * r := by
      nlinarith 
    calc
      (a * b * c : ℝ) = (a : ℝ) * (b : ℝ) * (c : ℝ) := by ring
      _ = (a : ℝ) * (b : ℝ) * (b : ℝ) * r := by
        rw [eq6]
        <;> ring 
      _ = (b : ℝ) ^ 3 := by 
        rw [eq5]
        <;> nlinarith
  have h8' : (b : ℝ) ^ 3 = (6 : ℝ) ^ 6 := by
    nlinarith 
  have h10 : (b : ℝ) = (36 : ℝ) := by
    have h11 : (b : ℝ) ^ 3 = (36 : ℝ) ^ 3 := by
      nlinarith
    have h12 : (b : ℝ) = (36 : ℝ) := by 
      have h13 : (b : ℝ) ^ 3 - (36 : ℝ) ^ 3 = 0 := by 
        linarith 
      have h14 : (b : ℝ) ^ 3 - (36 : ℝ) ^ 3 = (b - (36 : ℝ)) * ((b : ℝ) ^ 2 + (b : ℝ) * (36 : ℝ) + (36 : ℝ) ^ 2) := by
        ring 
      rw [h14] at h13 
      cases' (mul_eq_zero.1 h13) with h15 h16 
      · -- case h15 : b - 36 = 0 
        linarith 
      · -- case h16: b ^ 2 + 36 * b + 36^2 = 0 
        nlinarith [sq_nonneg (b + (36 : ℝ) / 2)]
    linarith 
  have hb36 : b = 36 := by 
    exact_mod_cast h10 
  have h82 : (a * b * c : ℝ) = (6 ^ 6 : ℝ) := by 
    nlinarith 
  have h81 : a * b * c = 6 ^ 6 := by 
    exact_mod_cast h82 
  rw [hb36] at h81 
  have h81 : a * 36 * c = 6 ^ 6 := by
    omega 
  have hm' : (36 : ℕ) - a = m ^ 2 := by
    have h102 : (b : ℕ) - a = m ^ 2 := by
      omega
    rw [hb36] at h102 
    omega 
  have h66 : a < 36 := by
    by_contra h
    push_neg at h
    have h7 : (a : ℝ) ≥ (36 : ℝ) := by
      exact_mod_cast h 
    have eq5 : (b : ℝ) = (a : ℝ) * r := by
      nlinarith 
    have eq8 : (b : ℝ) > (36 : ℝ) := by
      nlinarith
    nlinarith
  have h77 : m ≤ 5 := by
    by_contra h
    push_neg at h
    have h78 : m ≥ 6 := by 
      omega 
    have h79 : m ^ 2 ≥ 36 := by 
      nlinarith 
    have hm' : (36 : ℕ) - a = m ^ 2 := hm'
    omega 
  interval_cases m <;> try { 
    omega 
  }
  <;> try { 
    have h66 : a < 36 := h66
    interval_cases a <;> omega 
  }