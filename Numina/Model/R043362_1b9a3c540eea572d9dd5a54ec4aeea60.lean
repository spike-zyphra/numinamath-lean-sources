import Mathlib

theorem algebra_321352 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    IsLeast {z | ∃ x y, x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1 ∧ z = x / c ^ 2 + y ^ 2 / d ^ 2} (-|a| / c ^ 2) := by 
  constructor
  · -- First, show that -|a| / c^2 is in the set
    use -|a|, (0 : ℝ)
    constructor
    · -- Show that (-|a|) ^ 2 / a ^ 2 + (0 : ℝ) ^ 2 / b ^ 2 = 1
      have h1 : (-|a|) ^ 2 = a ^ 2 := by 
        have h2 : |a| ^ 2 = a ^ 2 := by 
          simp [abs_pow]
        nlinarith 
      rw [h1]
      field_simp [ha, hb]
      <;> nlinarith
    · -- Show that -|a| / c ^ 2 = (-|a|) / c ^ 2 + (0 : ℝ) ^ 2 / d ^ 2
      field_simp [hc, hd]
      <;> nlinarith 
  · -- Show that -|a| / c^2 is the least element in the set
    intro z h
    rcases h with ⟨x, y, h_eq, h_eq2⟩
    rw [h_eq2]
    have h11 : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1 := h_eq
    have h12 : x ^ 2 ≤ a ^ 2 := by 
      have h13 : x ^ 2 / a ^ 2 ≤ (1 : ℝ) := by 
        have eq1 : x ^ 2 / a ^ 2 = 1 - y ^ 2 / b ^ 2 := by
          field_simp at h11 ⊢ 
          nlinarith 
        rw [eq1] 
        have h14 : y ^ 2 / b ^ 2 ≥ 0 := by 
          apply div_nonneg 
          · -- Show that y ^ 2 ≥ 0 
            positivity 
          · -- Show that b ^ 2 ≥ 0 
            positivity 
        linarith 
      have h5 : a ^ 2 > 0 := by 
        exact sq_pos_of_ne_zero ha 
      have h7 : x ^ 2 / a ^ 2 = x ^ 2 / a ^ 2 := by rfl 
      have h8 : x ^ 2 ≤ a ^ 2 := by 
        apply (div_le_iff₀ (by positivity)).mp at h13 
        nlinarith 
      linarith 
    have h14 : -|a| ≤ x := by 
      have h16 : x^2 ≤ a^2 := h12
      cases' abs_cases a with ha1 ha1
      · -- Case where |a| = a, so a ≥ 0.
        cases' abs_cases x with hx hx
        · -- Case where x ≥ 0.
          nlinarith 
        · -- Case where x < 0.
          nlinarith
      · -- Case where |a| = -a, so a < 0.
        cases' abs_cases x with hx hx
        · -- Case where x ≥ 0.
          nlinarith 
        · -- Case where x < 0.
          nlinarith 
    have h17 : y ^ 2 / d ^ 2 ≥ 0 := by positivity
    have h18 : x / c ^ 2 ≥ -|a| / c ^ 2 := by 
      have h14' : x ≥ -|a| := h14
      have h19 : c ^ 2 > 0 := by positivity
      apply (div_le_div_right h19).mpr 
      nlinarith 
    have h19 : x / c ^ 2 + y ^ 2 / d ^ 2 ≥ -|a| / c ^ 2 := by
      have h20 : x / c ^ 2 ≥ -|a| / c ^ 2 := h18 
      have h21 : y ^ 2 / d ^ 2 ≥ 0 := by positivity 
      linarith [h20, h21]
    linarith