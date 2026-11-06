import Mathlib

theorem algebra_2265
    (x : ℝ)
    (hx : 2 * x + 1 = 0) :
    x < 0 ∧ ¬∃ n : ℤ, x = n := by
  have hx_val : x = -1 / 2 := by
    linarith
  constructor
  · -- Show that x < 0
    rw [hx_val]
    norm_num
  · -- Show that ¬∃ n : ℤ, x = n
    intro h
    rcases h with ⟨n, hn⟩
    rw [hx_val] at hn
    have h3 : (n : ℝ) = -1 / 2 := by
      linarith
    have h4 : n = -0 := by
      have h5 : (n : ℝ) = -1 / 2 := h3
      have h9 : (n * 2 : ℝ) = -1 := by
        linarith [h5]
      have h10 : (n * 2 : ℤ) = -1 := by
        exact_mod_cast h9
      omega
    norm_num [h4] at hn
    <;> norm_num at hn <;> try { tauto }
    <;> norm_num at hn <;> try { linarith }
    all_goals
      omega