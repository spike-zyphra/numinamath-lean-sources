import Mathlib

theorem algebra_128704 (a : ℝ) :
    (∃! x : ℝ, x^2 + 2 * a * x + 1 = 0) ↔ a = -1 ∨ a = 1 := by
  constructor
  · -- Assume there exists a unique x such that x^2 + 2 * a * x + 1 = 0, prove a = -1 ∨ a = 1
    intro h
    rcases h with ⟨x, ⟨h1, h2⟩⟩
    have h_eq1 : x^2 + 2 * a * x + 1 = 0 := h1
    have h_eq2 : ∀ y, y ^ 2 + 2 * a * y + 1 = 0 → y = x := h2
    have h_eq3 : (-2 * a - x) ^ 2 + 2 * a * (-2 * a - x) + 1 = 0 := by
      nlinarith [h_eq1]
    have h_eq4 : -2 * a - x = x := by
      apply h_eq2 (-2 * a - x) 
      exact h_eq3
    have h_eq5 : x = -a := by 
      linarith
    have h_eq6 : (-a) ^ 2 + 2 * a * (-a) + 1 = 0 := by
      rw [show x = -a by linarith [h_eq5] ] at h_eq1
      linarith
    have h_eq7 : a^2 = 1 := by 
      nlinarith
    have : a = 1 ∨ a = -1 := by
      have h : a^2 = 1 := h_eq7
      rw [sq_eq_one_iff] at h
      tauto
    cases this with
    | inl h1 => 
      right
      linarith
    | inr h2 => 
      left
      linarith
  · -- Assume a = -1 ∨ a = 1, prove ∃! x : ℝ, x^2 + 2 * a * x + 1 = 0
    rintro (ha | ha)
    · -- Case a = -1
      use 1
      constructor
      · -- Show 1^2 + 2 * (-1) * 1 + 1 = 0 
        rw [ha]
        norm_num
      · -- Show that for all y, if y^2 + 2 * (-1) * y + 1 = 0 then y = 1
        intro y hy
        rw [ha] at hy
        have h_eq : y ^ 2 - 2 * y + 1 = 0 := by
          linarith
        have : (y - 1) ^ 2 = 0 := by
          nlinarith
        have : y - 1 = 0 := by
          apply pow_eq_zero 
          exact this
        linarith
    · -- Case a = 1
      use -1
      constructor
      · -- Show (-1)^2 + 2 * 1 * (-1) + 1 = 0
        rw [ha]
        norm_num
      · -- Show that for all y, if y^2 + 2 * 1 * y + 1 = 0 then y = -1
        intro y hy
        rw [ha] at hy
        have h_eq : y ^ 2 + 2 * y + 1 = 0 := by
          linarith
        have : (y + 1) ^ 2 = 0 := by
          nlinarith
        have : y + 1 = 0 := by
          apply pow_eq_zero 
          exact this
        linarith