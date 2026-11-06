import Mathlib
/-let a,b,c be distinct real numbers satisfying the equations
a+1/b=b+1/c=c+1/a. prove that |abc|=1 -/
theorem algebra_2429 {a b c : ℝ} (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a + 1 / b = b + 1 / c)
(h1 : b + 1 / c = c + 1 / a) : |a * b * c| = 1 := by
  have h2 : a - b = (1 / c - 1 / b) := by linarith
  have h3 : b - c = (1 / a - 1 / c) := by linarith
  have h4 : (a - b) * (b * c) = b - c := by
    have h4 : (a - b) = (1 / c - 1 / b) := by linarith
    field_simp [hc, hb] at h4 ⊢
    nlinarith [h4]
  have h5 : (b - c) * (a * c) = c - a := by
    have h5 : (b - c) = (1 / a - 1 / c) := by linarith
    field_simp [ha, hc] at h5 ⊢
    nlinarith [h5]
  have h6 : (c - a) * (a * b) = a - b := by
    have h6 : c + 1 / a = a + 1 / b := by linarith
    field_simp [ha, hb] at h6 ⊢
    nlinarith [h6]
  -- need to show the Denominators are not zero 
  have h_ne : a - b ≠ 0 := by
    intro h
    apply habc.left
    linarith
  have h2_ne : b - c ≠ 0 := by
    intro h
    apply habc.right.right
    linarith
  have h3_ne : c - a ≠ 0 := by
    intro h
    apply habc.right.left
    linarith
  have eq1 : (a - b) * (b * c) = b - c := by linarith [h4]
  have eq2 : (b - c) * (a * c) = c - a := by linarith [h5]
  have eq3 : (c - a) * (a * b) = a - b := by linarith [h6]
  have eq4 : ((a - b) * (b * c)) * ((b - c) * (a * c)) * ((c - a) * (a * b)) = (b - c) * (c - a) * (a - b) := by
    rw [eq1, eq2, eq3]
  have eq5 : (a * b * c) ^ 2 * ((a - b) * (b - c) * (c - a)) = (a - b) * (b - c) * (c - a) := by
    have h7 : ((a - b) * (b * c)) * ((b - c) * (a * c)) * ((c - a) * (a * b)) = 
      (a * b * c) ^ 2 * ((a - b) * (b - c) * (c - a)) := by
        ring
    rw [h7] at eq4
    nlinarith [sq_nonneg (a * b * c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              h_ne, h2_ne, h3_ne]
  have h8 : (a * b * c) ^ 2 = 1 := by
    have h7 : (a - b) * (b - c) * (c - a) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      · exact h_ne
      · exact h2_ne
      · exact h3_ne
    have h9 : (a * b * c) ^ 2 * ((a - b) * (b - c) * (c - a)) - ((a - b) * (b - c) * (c - a)) = 0 := by linarith [eq5]
    have h10 : ((a * b * c) ^ 2 - 1) * ((a - b) * (b - c) * (c - a)) = 0 := by
      ring_nf at h9 ⊢
      linarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case $(a * b * c)^2 - 1 = 0$
      have : (a * b * c) ^ 2 = 1 := by linarith
      exact this
    · -- Case $(a - b) * (b - c) * (c - a) = 0$
      exfalso
      exact h7 (by linarith)
  have h9 : a * b * c = 1 ∨ a * b * c = -1 := by
    have h10 : (a * b * c) ^ 2 = 1 := by linarith [h8]
    have h11 : (a * b * c) = 1 ∨ (a * b * c) = -1 := by
      rw [sq_eq_one_iff] at h10
      exact h10
    exact h11
  cases' h9 with h10 h11
  · -- Case $a * b * c = 1$
    rw [h10]
    norm_num
  · -- Case $a * b * c = -1$
    rw [h11]
    norm_num