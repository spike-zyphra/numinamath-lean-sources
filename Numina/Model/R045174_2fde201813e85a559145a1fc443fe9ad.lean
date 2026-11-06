import Mathlib

theorem algebra_20171:
  IsGreatest {b | ∃a:ℝ, (a^2=49 ∧ (∀x:ℝ, a*x^2+b*x-6 < 0) ∧ ∃m:ℤ, b=m)} 12 := by
  constructor
  · -- Show that 12 is in the set.
    use (-7 : ℝ)
    constructor
    · -- Show that (-7) ^ 2 = 49.
      norm_num
    constructor
    · -- Show that for all real numbers x, -7*x^2 + 12*x - 6 < 0.
      intro x
      have h1 : (-7 : ℝ) * x ^ 2 + (12 : ℝ) * x - 6 < 0 := by
        nlinarith [sq_nonneg (x - 6 / 7), sq_nonneg ((-7 : ℝ) * x + 6), sq_nonneg (x + (-6 / 7)), sq_nonneg ((x * 7) - 6)]
      linarith
    · -- Show that there exists an integer m such that 12 = m.
      use 12
      all_goals norm_num
  · -- Show that 12 is the greatest element in the set.
    intro b hb
    rcases hb with ⟨a, ha1, h1, ⟨m, hm⟩⟩
    have h2 : a = 7 ∨ a = -7 := by
      have h3 : a ^ 2 = 49 := ha1
      have h4 : a = 7 ∨ a = -7 := by
        have h5 : a ^ 2 - 49 = 0 := by linarith
        have h6 : (a - 7) * (a + 7) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- Case a - 7 = 0
          left
          linarith
        · -- Case a + 7 = 0
          right
          linarith
      tauto
    cases h2 with
    | inl ha_pos =>
      have h_pos1 := h1 (x := 1)
      have h_pos2 := h1 (x := -1)
      rw [show a = 7 by linarith] at h_pos1 h_pos2
      nlinarith
    | inr ha_neg =>
      have h8 : a = -7 := by linarith [ha_neg]
      have h31 := h1 (x := 1)
      rw [show a = -7 by linarith] at h31
      have h31' : b < 13 := by
        nlinarith
      have h5 : m < 13 := by
        by_contra h
        push_neg at h
        have h6 : m ≥ 13 := by omega
        have h7 : (b : ℝ) ≥ (13 : ℝ) := by
          have h8 : (b : ℝ) = (↑m : ℝ) := by
            linarith [hm]
          rw [h8]
          exact_mod_cast (show m ≥ 13 by omega)
        linarith
      have h8 : m ≤ 12 := by omega
      have h9 : (b : ℝ) ≤ (12 : ℝ) := by
        have h10 : (b : ℝ) = (↑m : ℝ) := by
          linarith [hm]
        have h11 : (m : ℝ) ≤ (12 : ℝ) := by
          exact_mod_cast (show m ≤ 12 by omega)
        rw [h10]
        linarith
      linarith