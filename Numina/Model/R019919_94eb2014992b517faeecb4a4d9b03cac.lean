import Mathlib


open Real


lemma lemma_1 : ∀ (a b c : ℝ), (a ^ 2 * b ^ 3 * c < 0) → (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) := by
  intro a b c h
  have h1 : a ≠ 0 := by
    by_contra h11
    have h2 : a ^ 2 = 0 := by
      rw [h11]
      norm_num
    have h3 : a ^ 2 * b ^ 3 * c = 0 := by
      rw [h2]
      ring
    linarith
  have h4 : b ≠ 0 := by
    by_contra h41
    have h5 : b ^ 3 = 0 := by
      rw [h41]
      norm_num
    have h6 : a ^ 2 * b ^ 3 * c = 0 := by
      rw [h5]
      ring
    linarith
  have h7 : c ≠ 0 := by
    by_contra h71
    have h8 : a ^ 2 * b ^ 3 * c = 0 := by
      rw [h71]
      ring
    linarith
  exact ⟨h1, h4, h7⟩


theorem algebra_3487 :
  IsLeast {x : ℝ | ∃ a b c : ℝ, x = (a + 2 * c) / abs b + (a + b) / abs c + (b + 2 * c) / abs a ∧ a + b + 2 * c = 0 ∧ a^2 * b^3 * c < 0} (-2) := by
  constructor
  · -- Show that -2 is in the set
    use 1 / 2, -1, 1 / 4
    constructor
    · -- Show that the value is -2
      norm_num [abs_of_neg, abs_of_pos]
      all_goals
        norm_num
    constructor
    · -- Show that 1/2 + (-1) + 2*(1/4) = 0
      norm_num
    · -- Show that (1/2)^2 * (-1)^3 * (1/4) < 0
      norm_num
  · -- Show that -2 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, hx_eq, h_eq, h_neg⟩
    have h1 : a ≠ 0 := (lemma_1 a b c h_neg).1
    have h2 : b ≠ 0 := (lemma_1 a b c h_neg).2.1
    have h3 : c ≠ 0 := (lemma_1 a b c h_neg).2.2
    have h_eq1 : a + 2 * c = -b := by
      linarith 
    have h_eq2 : a + b = -2 * c := by
      linarith
    have h_eq3 : b + 2 * c = -a := by
      linarith

    have eq1 : (a + 2 * c) / abs b = (-b) / abs b := by
      rw [h_eq1]
    have eq2 : (a + b) / abs c = (-2 * c) / abs c := by
      rw [h_eq2]
      <;> ring
    have eq3 : (b + 2 * c) / abs a = (-a) / abs a := by
      rw [h_eq3]
      <;> ring
    have hx_eq2 : x = (-b) / abs b + (-2 * c) / abs c + (-a) / abs a := by
      rw [hx_eq]
      rw [eq1, eq2, eq3]
      <;> ring
    have h4 : b ^ 3 * c < 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), h_neg]
    by_contra h
    push_neg at h
    have hb1 : b > 0 ∨ b < 0 := by 
      by_contra h
      push_neg at h 
      have : b = 0 := by nlinarith 
      tauto 
    have hc1 : c > 0 ∨ c < 0 := by 
      by_contra h
      push_neg at h 
      have : c = 0 := by nlinarith 
      tauto
    rcases hb1 with hbpos | hbneg 
    · -- b > 0 
      have hb2 : abs b = b := abs_of_pos hbpos 
      have hc1 : c < 0 := by 
        nlinarith [sq_pos_of_pos hbpos, sq_nonneg (b ^ 2), sq_nonneg (c), h4]
      have hc2 : abs c = -c := abs_of_neg hc1 
      have eqx : x = -1 + 2 + (-a) / abs a := by
        rw [hx_eq2]
        rw [hb2] 
        rw [hc2] 
        field_simp 
        <;> ring 
      have ha1 : a < 0 ∨ a > 0 := by 
        by_contra h
        push_neg at h
        have ha0 : a = 0 := by nlinarith 
        tauto 
      rcases ha1 with ha1l | ha1r 
      · -- a < 0 
        have ha2 : abs a = -a := abs_of_neg ha1l 
        have eq2 : (-a) / abs a = 1 := by 
          rw [ha2]
          field_simp [show a ≠ 0 by assumption]
          <;> nlinarith
        rw [eq2] at eqx 
        nlinarith 
      · -- a > 0 
        have ha2 : abs a = a := abs_of_pos ha1r 
        have eq2 : (-a) / abs a = -1 := by 
          rw [ha2]
          field_simp 
          <;> nlinarith
        rw [eq2] at eqx 
        nlinarith
    · -- b < 0 
      have hb2 : abs b = -b := abs_of_neg hbneg 
      have hc1 : c > 0 := by 
        nlinarith [sq_nonneg (b ^ 2), sq_nonneg (c), h4]
      have hc2 : abs c = c := abs_of_pos hc1
      have eqx : x = 1 - 2 + (-a) / abs a := by 
        rw [hx_eq2]
        rw [hb2]
        rw [hc2]
        field_simp 
        <;> ring 
      have ha1 : a < 0 ∨ a > 0 := by 
        by_contra h
        push_neg at h
        have ha0 : a = 0 := by nlinarith 
        tauto 
      rcases ha1 with ha1l | ha1r 
      · -- a < 0 
        have ha2 : abs a = -a := abs_of_neg ha1l 
        have eq2 : (-a) / abs a = 1 := by
          rw [ha2]
          field_simp [show a ≠ 0 by assumption]
          <;> nlinarith
        rw [eq2] at eqx 
        nlinarith 
      · -- a > 0 
        have ha2 : abs a = a := abs_of_pos ha1r 
        have eq2 : (-a) / abs a = -1 := by 
          rw [ha2]
          field_simp 
          <;> nlinarith 
        rw [eq2] at eqx 
        nlinarith