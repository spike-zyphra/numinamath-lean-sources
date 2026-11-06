import Mathlib

theorem algebra_264524 {x : ℝ} (hx : x ≠ 3) (h : 3 / (x - 3) + 5 / (2 * x - 6) = 11 / 2) :
    2 * x - 6 = 2 := by 
  have h1 : 2 * x - 6 = 2 * (x - 3) := by
    nlinarith
  have h2 : 3 / (x - 3) + 5 / (2 * (x - 3)) = 11 / 2 := by
    have eq1 : 2 * x - 6 = 2 * (x - 3) := h1
    rw [eq1] at h
    exact h

  have hx3 : x - 3 ≠ 0 := by
    intro h'
    apply hx
    linarith

  have eq1 : (3 / (x - 3) + 5 / (2 * (x - 3))) * (2 * (x - 3)) = 11 := by
    have eq2 : (3 / (x - 3) + 5 / (2 * (x - 3))) * (2 * (x - 3)) = 6 + 5 := by
      have eq3 : 3 / (x - 3) + 5 / (2 * (x - 3)) = (3 * 2 + 5) / (2 * (x - 3)) := by
        field_simp [hx3, show 2 * (x - 3) ≠ 0 by
          intro h'
          apply hx3
          linarith
        ]
        <;> ring_nf
        <;> field_simp
        <;> ring
        all_goals try { tauto }
      rw [eq3]
      have hx3' : 2 * (x - 3) ≠ 0 := by
        intro h'
        apply hx3
        linarith
      field_simp [hx3']
      <;> ring_nf
      <;> linarith
      all_goals try { tauto }
    linarith [eq2]

  have eq2 : (3 / (x - 3) + 5 / (2 * (x - 3))) * (2 * (x - 3)) = (11 / 2) * (2 * (x - 3)) := by
    have eq3 : 3 / (x - 3) + 5 / (2 * (x - 3)) = 11 / 2 := h2
    rw [eq3]
    all_goals linarith

  have h3 : (11 : ℝ) = 11 * (x - 3) := by
    have eq1' : (3 / (x - 3) + 5 / (2 * (x - 3))) * (2 * (x - 3)) = 11 := eq1
    have eq4 : (3 / (x - 3) + 5 / (2 * (x - 3))) * (2 * (x - 3)) = (11 / 2) * (2 * (x - 3)) := eq2
    have eq5 : (11 / 2 : ℝ) * (2 * (x - 3)) = 11 * (x - 3) := by
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> norm_num
      all_goals try { tauto }
    linarith [eq1', eq4, eq5]
    all_goals try { tauto }

  have h4 : x - 3 = 1 := by
    have hx3 : x - 3 ≠ 0 := hx3
    apply (mul_left_inj' (show (11 : ℝ) ≠ 0 by norm_num)).mp
    linarith
    all_goals linarith
    all_goals try { tauto }
    all_goals try { nlinarith }

  have h5 : 2 * x - 6 = 2 := by
    have h6 : x - 3 = 1 := h4
    linarith [h6]
  linarith [h5]
  all_goals try { tauto }