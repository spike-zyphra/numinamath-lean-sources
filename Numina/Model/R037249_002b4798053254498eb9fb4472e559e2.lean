import Mathlib

theorem algebra_314941 {a b c : ℝ} (ha : a + b + c = 0) (hb : a * b * c = 2) (hc : c > 0) :
    abs a + abs b ≥ 2 := by
  have h1 : a + b = -c := by
    linarith 
  have h2 : a * b = 2 / c := by 
    have h11 : c ≠ 0 := by linarith
    have h12 : a * b * c = 2 := by linarith [hb]
    field_simp [h11] at h12 ⊢
    nlinarith
  -- We now show that c ≥ 2, by showing that c^3 - 8 ≥ 0. 
  have h3 : (a - b) ^ 2 ≥ 0 := by 
    apply sq_nonneg 
  have h4 : (a - b) ^ 2 = c ^ 2 - 8 / c := by 
    have h5 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by
      nlinarith
    rw [h5, h1, h2]
    all_goals 
      field_simp at *
      <;> ring 
  have h5 : c ≥ 2 := by 
    have h6 : c ^ 2 - 8 / c ≥ 0 := by
      nlinarith [h4, h3]
    have h7 : c ^ 3 ≥ 8 := by
      have h8 : c ^ 2 - 8 / c ≥ 0 := h6 
      have h9 : c > 0 := hc
      have h11 : c ^ 2 - 8 / c = (c ^ 3 - 8) / c := by
        field_simp 
        <;> ring 
      rw [h11] at h8 
      apply (div_nonneg_iff).mp at h8 
      cases h8 with
      | inl h81 => 
        nlinarith 
      | inr h82 => 
        nlinarith 
    have h8 : c ≥ 2 := by 
      nlinarith [sq_nonneg (c ^ 2 - 4), sq_nonneg (c - 2)]
    linarith 
  -- Now that we know c ≥ 2, we can compute |a| + |b|.
  have h8 : abs a + abs b ≥ 2 := by
    cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> try { 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c ^ 2 - 4), sq_nonneg (c - 2), mul_pos (show 0 < c by linarith) (show 0 < c by linarith)]
    }
  linarith