import Mathlib

theorem algebra_184985 {a b c : ℝ} (h : a * b / (a * c) = 5 / 3 ∧ a * c / (b * c) = 3 / 1) :
    (a ^ 5 * b ^ 2 / c ^ 3) / (a ^ 3 * b ^ 5 / c ^ 4) = 27 / 5 := by
  rcases h with ⟨h1, h2⟩
  have ha1 : a ≠ 0 := by
    by_contra h'
    rw [h'] at h1 h2
    norm_num [h'] at h1 h2 
    all_goals linarith
  have hb1 : b ≠ 0 := by
    by_contra h'
    rw [h'] at h1 h2
    norm_num [h'] at h1 h2 
    all_goals linarith
  have hc1 : c ≠ 0 := by
    by_contra h'
    rw [h'] at h1 h2
    norm_num [h'] at h1 h2 
    all_goals linarith
  have h1' : b / c = 5 / 3 := by 
    have hne1 : a * c ≠ 0 := by
      apply mul_ne_zero
      exact ha1
      exact hc1
    have hne2 : c ≠ 0 := hc1
    have eq1 : a * b / (a * c) = b / c := by 
      have hne1' : a ≠ 0 := ha1
      have hne2' : c ≠ 0 := hc1
      field_simp [hne1', hne2']
      <;> ring_nf <;> field_simp [hne1', hne2']
      <;> ring
    rw [eq1] at h1 
    all_goals linarith
  have h3 : 3 * b = 5 * c := by 
    have hc1' : c ≠ 0 := hc1
    field_simp at h1' ⊢
    all_goals nlinarith
  have h4 : a / b = 3 := by 
    have hne2 : b * c ≠ 0 := by
      apply mul_ne_zero
      exact hb1
      exact hc1
    have hne3 : b ≠ 0 := hb1
    have hne4 : c ≠ 0 := hc1
    have eq2 : a * c / (b * c) = a / b := by
      have hne3' : b ≠ 0 := hb1
      have hne4' : c ≠ 0 := hc1
      field_simp [hne3', hne4']
      <;> ring_nf <;> field_simp [hne3', hne4']
      <;> ring
    rw [eq2] at h2 
    norm_num at h2 ⊢
    all_goals linarith
  have h5 : a = 3 * b := by 
    have hb1' : b ≠ 0 := hb1
    field_simp at h4 ⊢
    all_goals nlinarith
  have h6 : c = (3 / 5) * b := by 
    linarith
  have h7 : (a ^ 5 * b ^ 2 / c ^ 3) / (a ^ 3 * b ^ 5 / c ^ 4) = (a ^ 2 * c) / (b ^ 3) := by 
    field_simp [hc1, ha1, hb1]
    <;> ring_nf
    <;> field_simp [hc1, ha1, hb1]
    <;> ring
  rw [h7]
  rw [show a = 3 * b by linarith [h5]]
  rw [show c = (3 / 5) * b by linarith [h6]]
  have hb2 : b ^ 3 ≠ 0 := by
    have hb1' : b ≠ 0 := hb1
    have hne2 : b ^ 3 ≠ 0 := by
      apply pow_ne_zero 
      exact hb1 
    assumption
  field_simp [hb2]
  <;> ring_nf
  <;> nlinarith [sq_pos_of_ne_zero hb1]