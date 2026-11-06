import Mathlib

/-determine all positive real solutions of the following system of equations:
a = max {1 / b, 1 / c}
b = max {1 / c, 1 / d}
c = max {1 / d, 1 / e}
d = max {1 / e, 1 / f}
e = max {1 / f, 1 / a}
f = max {1 / a, 1 / b}-/

theorem algebra_262162: {(a, b, c, d, e, f): ℝ × ℝ × ℝ × ℝ × ℝ × ℝ | 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < e ∧ 0 < f ∧
  a = max (1 / b) (1 / c) ∧ b = max (1 / c) (1 / d) ∧ c = max (1 / d) (1 / e) ∧ d = max (1 / e) (1 / f) ∧
  e = max (1 / f) (1 / a) ∧ f = max (1 / a) (1 / b) ∧ a = max a (max b (max c (max d (max e f))))} =
    {(a, b, c, d, e, f): ℝ × ℝ × ℝ × ℝ × ℝ × ℝ | ∃ x, 1 ≤ x ∧ ((a = x ∧ b = x ∧ c = 1 / x ∧ d = x ∧ e = x ∧ f = 1 / x)
    ∨ (a = x ∧ b = 1 / x ∧ c = x ∧ d = x ∧ e = 1 / x ∧ f = x))} := by

    ext ⟨a, b, c, d, e, f⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨ha, hb, hc, he, hf, l1, l2, l3, l4, l5, l6, s1, s2, s3, s4, s5⟩
      simp

      -- then we can compute f and e directly
      have h1: f = 1 / b := by
        rw [l6]
        simp
        field_simp
        apply one_div_le_one_div_of_le
        tauto
        tauto
      have h2: e = b := by
        rw [l5]
        rw [show b = f⁻¹ by simp [h1]]
        simp
        field_simp
        apply one_div_le_one_div_of_le
        tauto
        tauto
      simp [h1, h2] at *
      clear hf he l6 l5 h1 h2

      by_cases s: 1 ≤ b

      -- case 1: 1 ≤ b
      .
        have h3: d = b := by
          rw [l4]
          simp
          field_simp
          suffices 1 / b ≤ 1 / 1 by linarith
          apply one_div_le_one_div_of_le
          norm_num
          tauto
        simp [h3] at *
        clear l4 s4 s3
        simp [l3] at *
        clear hc l2 s5 h3 l3
        have h4: a = b := by
          rw [l1]
          simp
          field_simp
          suffices 1 / b ≤ 1 / 1 by linarith
          apply one_div_le_one_div_of_le
          norm_num
          tauto
        simp [h4] at *
        use b
        simp [s]

      -- case 2: b < 1
      .
        simp at s
        have h3: d = 1 / b := by
          rw [l4]
          simp
          field_simp
          suffices 1 / 1 ≤ 1 / b by linarith
          apply one_div_le_one_div_of_le
          tauto
          linarith
        simp [h3] at *
        clear s5 s4 h3
        have h4: c = 1 / b := by
          rw [l3]
          simp
          exact l4
        simp [h4] at *
        have h5: a = 1 / b := by
          rw [l1]
          simp
          exact l3
        simp [h5] at *
        use b⁻¹
        have o: 1 ≤ b⁻¹ := by
          field_simp
          nth_rewrite 1 [show (1: ℝ) = 1 / 1 by norm_num]
          apply one_div_le_one_div_of_le
          tauto
          linarith
        simp [o]


    -- the backward direction
    .
      intro h
      simp at h
      obtain ⟨x, hx, h⟩ := h
      have f: x⁻¹ ≤ x := by
        field_simp
        suffices 1 / x ≤ 1 / 1 by linarith
        apply one_div_le_one_div_of_le
        norm_num
        linarith
      rcases h with h | h
      .
        simp [h]
        constructor
        .
          linarith
        .
          exact f
      .
        simp [h]
        constructor
        .
          linarith
        .
          exact f
          