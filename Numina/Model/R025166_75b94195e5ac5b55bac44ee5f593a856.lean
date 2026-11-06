import Mathlib

theorem algebra_201118 {a b c : ℝ} (ha : a ≠ 0) (hroots : ∃ x1 x2 x3, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    a * x1^5 + b * x1^4 + c = 0 ∧ a * x2^5 + b * x2^4 + c = 0 ∧ a * x3^5 + b * x3^4 + c = 0) :
    ∃ x1 x2 x3, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ c * x1^5 + b * x1 + a = 0 ∧ c * x2^5 + b * x2 + a = 0 ∧
    c * x3^5 + b * x3 + a = 0 := by

  obtain ⟨x1, x2, x3, h12, h23, h31, h1, h2, h3⟩ := hroots

  have hc : c ≠ 0 := by
    by_contra h
    have h1' : a * x1^5 + b * x1^4 + c = 0 := h1
    rw [h] at h1'
    have h1_eq : a * x1^5 + b * x1^4 = 0 := by linarith
    have h2' : a * x2^5 + b * x2^4 + c = 0 := h2
    rw [h] at h2'
    have h2_eq : a * x2^5 + b * x2^4 = 0 := by linarith
    have h3' : a * x3^5 + b * x3^4 + c = 0 := h3
    rw [h] at h3'
    have h3_eq : a * x3^5 + b * x3^4 = 0 := by linarith
    have eq1 : x1^4 * (a * x1 + b) = 0 := by
      nlinarith
    have eq2 : x2^4 * (a * x2 + b) = 0 := by
      nlinarith
    have eq3 : x3^4 * (a * x3 + b) = 0 := by
      nlinarith
    have h10 : x1 = 0 ∨ x1 = -b / a := by
      cases (mul_eq_zero.1 eq1) with
      | inl h =>
        have h10 : x1 = 0 := by
          have h11 : x1^4 = 0 := by
            linarith
          have : x1 = 0 := by
            simp at h11 ⊢
            <;> nlinarith
          linarith
        left; linarith
      | inr h =>
        right
        field_simp
        linarith
    have h20 : x2 = 0 ∨ x2 = -b / a := by
      cases (mul_eq_zero.1 eq2) with
      | inl h =>
        have h10 : x2 = 0 := by
          have h11 : x2^4 = 0 := by
            linarith
          have : x2 = 0 := by
            simp at h11 ⊢
            <;> nlinarith
          linarith
        left; linarith
      | inr h =>
        right
        field_simp
        linarith
    have h30 : x3 = 0 ∨ x3 = -b / a := by
      cases (mul_eq_zero.1 eq3) with
      | inl h =>
        have h10 : x3 = 0 := by
          have h11 : x3^4 = 0 := by
            linarith
          have : x3 = 0 := by
            simp at h11 ⊢
            <;> nlinarith
          linarith
        left; linarith
      | inr h =>
        right
        field_simp
        linarith
    cases h10 with
    | inl hx10 =>
      cases h20 with
      | inl hx20 =>
        exfalso
        have : x1 = x2 := by linarith
        have hneq : x1 ≠ x2 := h12
        contradiction
      | inr hx20 =>
        cases h30 with
        | inl hx30 =>
          exfalso
          have : x3 = x1 := by linarith
          have hneq : x3 ≠ x1 := by
            tauto
          contradiction
        | inr hx30 =>
          exfalso
          have : x2 = x3 := by linarith
          have hneq : x2 ≠ x3 := h23
          contradiction
    | inr hx10 =>
      cases h20 with
      | inl hx20 =>
        cases h30 with
        | inl hx30 =>
          exfalso
          have : x2 = x3 := by linarith
          have hneq : x2 ≠ x3 := h23
          contradiction
        | inr hx30 =>
          exfalso
          have : x3 = x1 := by linarith
          have hneq : x3 ≠ x1 := by
            tauto
          contradiction
      | inr hx20 =>
        exfalso
        have : x1 = x2 := by linarith
        have hneq : x1 ≠ x2 := h12
        contradiction

  have hx1 : x1 ≠ 0 := by
    by_contra h
    have h1' : a * x1^5 + b * x1^4 + c = 0 := h1
    rw [h] at h1'
    have hc' : c = 0 := by nlinarith
    contradiction

  have hx2 : x2 ≠ 0 := by
    by_contra h
    have h2' : a * x2^5 + b * x2^4 + c = 0 := h2
    rw [h] at h2'
    have hc' : c = 0 := by nlinarith
    contradiction

  have hx3 : x3 ≠ 0 := by
    by_contra h
    have h3' : a * x3^5 + b * x3^4 + c = 0 := h3
    rw [h] at h3'
    have hc' : c = 0 := by nlinarith
    contradiction

  use 1 / x1, 1 / x2, 1 / x3

  constructor
  · -- Show that 1/x1 ≠ 1/x2
    by_contra h
    have h4 : 1 / x1 = 1 / x2 := by linarith
    have h5 : x1 = x2 := by
      field_simp [hx1, hx2] at h4 ⊢
      all_goals linarith
    have hneq : x1 ≠ x2 := h12
    contradiction

  constructor
  · -- Show that 1/x2 ≠ 1/x3
    by_contra h
    have h4 : 1 / x2 = 1 / x3 := by linarith
    have h5 : x2 = x3 := by
      field_simp [hx2, hx3] at h4 ⊢
      all_goals linarith
    have hneq : x2 ≠ x3 := h23
    contradiction

  constructor
  · -- Show that 1/x3 ≠ 1/x1
    by_contra h
    have h4 : 1 / x3 = 1 / x1 := by linarith
    have h5 : x3 = x1 := by
      field_simp [hx3, hx1] at h4 ⊢
      all_goals linarith
    have hneq : x3 ≠ x1 := by
      tauto
    contradiction

  constructor
  · -- Show that c * (1/x1)^5 + b * (1/x1) + a = 0
    have eq1 : c * (1 / x1)^5 + b * (1 / x1) + a = 0 := by
      have hx1' : x1 ≠ 0 := hx1
      have eq1 : c + b * x1^4 + a * x1^5 = 0 := by 
        nlinarith [h1]
      have eq2 : c * (1 / x1) ^ 5 + b * (1 / x1) + a = (c + b * x1^4 + a * x1^5) / (x1^5) := by
        field_simp [hx1']
        <;> ring
      rw [eq2]
      rw [eq1]
      all_goals
        norm_num [hx1']
    linarith [eq1]

  constructor
  · -- Show that c * (1/x2)^5 + b * (1/x2) + a = 0
    have eq2 : c * (1 / x2)^5 + b * (1 / x2) + a = 0 := by
      have hx2' : x2 ≠ 0 := hx2
      have eq1 : c + b * x2^4 + a * x2^5 = 0 := by 
        nlinarith [h2]
      have eq2 : c * (1 / x2) ^ 5 + b * (1 / x2) + a = (c + b * x2^4 + a * x2^5) / (x2^5) := by
        field_simp [hx2']
        <;> ring
      rw [eq2]
      rw [eq1]
      all_goals
        norm_num [hx2']
    linarith [eq2]

  · -- Show that c * (1/x3)^5 + b * (1/x3) + a = 0
    have eq3 : c * (1 / x3)^5 + b * (1 / x3) + a = 0 := by
      have hx3' : x3 ≠ 0 := hx3
      have eq1 : c + b * x3^4 + a * x3^5 = 0 := by 
        nlinarith [h3]
      have eq2 : c * (1 / x3) ^ 5 + b * (1 / x3) + a = (c + b * x3^4 + a * x3^5) / (x3^5) := by
        field_simp [hx3']
        <;> ring
      rw [eq2]
      rw [eq1]
      all_goals
        norm_num [hx3']
    linarith [eq3]