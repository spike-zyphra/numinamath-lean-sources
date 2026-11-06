import Mathlib

theorem algebra_275383 {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a / b = 3) (h2 : b / c = 2) :
    (a - b) / (c - b) = -4 := by 
  have h3 : a = 3 * b := by
    field_simp at h1
    linarith
  have h4 : b = 2 * c := by
    field_simp at h2
    linarith
  have h5 : a = 6 * c := by
    rw [h3]
    linarith [h4]
  have h6 : a - b = 4 * c := by
    linarith [h5, h4]
  have h7 : c - b = -c := by 
    linarith [h4]
  -- Compute the final answer
  calc 
    (a - b) / (c - b) = (4 * c) / (-c) := by
      rw [h6, h7]
    _ = (4 * c) / (-c) := by rfl
    _ = -4 := by 
      have hc' : c ≠ 0 := hc
      field_simp [hc']
      <;> ring_nf
      <;> field_simp [hc']
      <;> ring_nf
      <;> field_simp [hc']
      <;> try (field_simp <;> ring_nf <;> field_simp)
      <;> norm_num
      <;> tauto
      <;> field_simp [hc']
      <;> ring_nf
      <;> try tauto
      all_goals try (field_simp [hc'] <;> norm_num)
      <;> try (ring_nf <;> field_simp [hc'] <;> norm_num)
      <;> try tauto
      all_goals try (field_simp [show c ≠ 0 by assumption, show b ≠ 0 by assumption] <;> ring_nf)
      <;> try { tauto }
      <;> field_simp [show c ≠ 0 by assumption, show b ≠ 0 by assumption]
      <;> ring_nf
      <;> try { linarith }
      <;> try { field_simp [show c ≠ 0 by assumption, show b ≠ 0 by assumption] }
      all_goals try (field_simp <;> norm_num)
      <;> try { tauto }
      all_goals try { nlinarith }