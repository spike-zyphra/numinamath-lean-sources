import Mathlib

theorem algebra_232908 (x : ℝ) (hx : x ≠ 0) : 128/x + 75/x + 57/x = 6.5 ↔ x = 40 := by
  constructor
  · -- Assume 128/x + 75/x + 57/x = 6.5, prove x = 40
    intro h_eq
    have h1 : (128 + 75 + 57) / x = 6.5 := by
      have h_eq1 : (128 + 75 + 57) / x = 128/x + 75/x + 57/x := by
        field_simp [hx]
        <;> ring_nf <;> field_simp [hx] <;> norm_num <;> try { ring }
        <;> try { field_simp [hx] }
      linarith [h_eq1, h_eq]
    have h2 : (260 : ℝ) / x = 6.5 := by 
      norm_num at h1 ⊢ 
      linarith
    have h3 : x = 40 := by 
      field_simp at h2 ⊢
      <;> nlinarith <;> try { 
        field_simp at h2 ⊢ 
        <;> nlinarith 
      } 
    exact h3
  · -- Assume x = 40, prove 128/x + 75/x + 57/x = 6.5
    intro h_eq
    rw [h_eq]
    norm_num
    <;> ring_nf <;> norm_num
    <;> try { ring }
    <;> try { norm_num }
    <;> try { linarith }
    <;> try { ring }
    all_goals norm_num
    <;> try { 
      norm_num at * 
      <;> try { linarith } 
    } 
    <;> try { ring_nf }
    all_goals try { tauto }
    all_goals try { linarith }
    all_goals try { norm_num }
    <;> try { ring_nf }
    all_goals try { nlinarith }
    <;> try { tauto }