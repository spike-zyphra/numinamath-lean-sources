import Mathlib

theorem algebra_136599 (a : ℝ) (ha : -2 ≤ a) (B C : Set ℝ)
    (hB : B = {y | ∃ x, y = 2 * x + 3 ∧ -2 ≤ x ∧ x ≤ a})
    (hC : C = {t | ∃ x, t = x ^ 2 ∧ -2 ≤ x ∧ x ≤ a}) :
    C ⊆ B ↔ 1 / 2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Assume $C \subseteq B$, prove $\frac{1}{2} \leq a \wedge a \leq 3$.
    intro h
    have h4 : (4 : ℝ) ∈ C := by
      rw [hC]
      use -2
      constructor 
      · -- Show that 4 = (-2) ^ 2 
        norm_num 
      constructor 
      · -- Show that -2 ≤ -2 
        norm_num 
      · -- Show that -2 ≤ a 
        linarith 
    have h7 : (4 : ℝ) ∈ B := h h4 
    rw [hB] at h7 
    rcases h7 with ⟨x, hx_eq, hx1, hx2⟩
    have h1 : 1 / 2 ≤ a := by
      have h8 : x = 1 / 2 := by 
        nlinarith 
      have hx2' : x ≤ a := by linarith
      rw [h8] at hx2' 
      linarith
    have h2 : a ≤ 3 := by
      by_cases ha2 : a ≤ 2
      · -- If a ≤ 2, maximum of x^2 in C is 4.
        have h8 : (4 : ℝ) ∈ C := by
          rw [hC]
          use -2 
          constructor 
          · -- Show that 4 = (-2) ^ 2 
            norm_num 
          constructor 
          · -- Show that -2 ≤ -2 
            norm_num 
          · -- Show that -2 ≤ a 
            linarith 
        have h9 : (4 : ℝ) ∈ B := h h8 
        rw [hB] at h9 
        rcases h9 with ⟨x, hx_eq, hx1, hx2⟩ 
        have h10 : x = 1 / 2 := by 
          nlinarith 
        have hx2' : x ≤ a := hx2 
        rw [h10] at hx2' 
        nlinarith 
      · -- a > 2. Then maximum of x^2 is a^2.
        have h8 : (a ^ 2 : ℝ) ∈ C := by 
          rw [hC]
          use a 
          all_goals nlinarith 
        have h9 : (a ^ 2 : ℝ) ∈ B := h h8 
        rw [hB] at h9 
        rcases h9 with ⟨x, hx_eq, hx1, hx2⟩ 
        have h5 : x = (a ^ 2 - 3) / 2 := by 
          linarith 
        have hx2' : x ≤ a := hx2 
        rw [h5] at hx2' 
        nlinarith 
    constructor 
    · -- Show that  1 / 2 ≤ a
      linarith [h1]
    · -- Show that a ≤ 3
      linarith [h2] 
  · -- Assume $\frac{1}{2} \leq a \wedge a \leq 3$, prove $C \subseteq B$.
    rintro ⟨ha1, ha2⟩
    intro t ht 
    rw [hC] at ht 
    rcases ht with ⟨x, ht_eq, hx1, hx2⟩ 
    rw [hB]
    use (t - 3) / 2
    constructor 
    · -- Show that t = 2 * ((t - 3) / 2) + 3.
      linarith
    constructor 
    · -- Show that -2 ≤ (t - 3) / 2
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x * 1 / 2 - 1), sq_nonneg (x * (a - 3)), sq_nonneg ((a - 3) * (a - 3 / 2)), sq_nonneg (a - 2), mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ 3 - a by linarith)]
    · -- Show that (t - 3) / 2 ≤ a 
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x * 1 / 2 - 1), sq_nonneg (x * (a - 3)), sq_nonneg ((a - 3) * (a - 3 / 2)), sq_nonneg (a - 2), mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ 3 - a by linarith)]