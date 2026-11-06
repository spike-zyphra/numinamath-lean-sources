import Mathlib

theorem calculus_128657 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (|x + 1 / 5| < δ ∧ x ≠ -1 / 5) → |(15 * x ^ 2 - 2 * x - 1) / (x + 1 / 5) + 8| < ε := by
  use ε / 15
  constructor
  · -- Show δ > 0
    linarith 
  · -- Show that for all x, if |x + 1/5| < δ and x ≠ -1/5, then |f(x) + 8| < ε
    intro x h 
    rcases h with ⟨h1, hx1⟩ 
    have h2 : x + 1 / 5 ≠ 0 := by 
      by_contra h'
      have h3 : x = -1 / 5 := by linarith
      contradiction
    have h4 : x + 1 / 5 ≠ 0 := h2
    have h33 : (15 * x ^ 2 - 2 * x - 1) / (x + 1 / 5) = 15 * x - 5 := by
      have h555 : (5 * x + 1) ≠ 0 := by
        by_contra h
        have h6 : x = -1 / 5 := by linarith
        tauto
      have h666 : (x + 1 / 5 : ℝ) = (5 * x + 1) / 5 := by ring
      rw [h666]
      have h777 : (5 * x + 1 : ℝ) ≠ 0 := h555
      field_simp [h777]
      <;> ring_nf
      <;> field_simp [h777]
      <;> ring_nf <;> nlinarith
      all_goals try { tauto }
    have h44 : |(15 * x ^ 2 - 2 * x - 1) / (x + 1 / 5) + 8| = 15 * |x + 1 / 5| := by 
      rw [h33]
      have h77 : |(15 * x - 5 + 8 : ℝ)| = 15 * |x + 1 / 5| := by 
        have h88 : (15 * x - 5 + 8 : ℝ) = 15 * (x + 1 / 5) := by
          ring_nf
        rw [h88]
        rw [abs_mul]
        norm_num 
        all_goals try { ring_nf } <;> try { norm_num }
      exact_mod_cast h77
    rw [h44] 
    have hx8 : |x + 1 / 5| < ε / 15 := h1 
    have hx9 : (15 * |x + 1 / 5| : ℝ) < ε := by
      linarith [abs_nonneg (x + 1 / 5), hx8] 
    linarith
    all_goals try { tauto }
    all_goals try { tauto }