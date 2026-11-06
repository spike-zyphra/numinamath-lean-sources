import Mathlib

theorem algebra_611550 :
    { t | ∃ a b c d : ℝ, ∃ m : ℝ → ℝ, ∃ x : ℝ, (c ≠ 0 ∨ d ≠ 0) ∧ t = a + d ∧
    (m = fun x ↦ (a * x + b) / (c * x + d)) ∧ x = m (m x) ∧ x ≠ m x ∧ c * x + d ≠ 0 ∧ c * m x + d ≠ 0} =
    { 0 } := by
  ext t 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume there exists such a,b,c,d,m,x, prove t = 0.
    intro h 
    rcases h with ⟨a, b, c, d, m, x, hcd, ht, hm_def, hx1, hx2, hx3, hx4⟩
    have eq11 : m x = (a * x + b) / (c * x + d) := by 
      simp [hm_def]
    have eq12 : m (m x) = (a * (m x) + b) / (c * (m x) + d) := by 
      simp [hm_def]
    have eq13 : x = m (m x) := by linarith [hx1]
    -- The equation from x = m(m x)
    have eq14 : x = (a * (m x) + b) / (c * (m x) + d) := by
      have eq22 : m (m x) = (a * (m x) + b) / (c * (m x) + d) := eq12
      have eq14 : x = m (m x) := eq13
      rw [eq22] at eq14
      linarith 
    -- From cross multiply.
    have eq15 : x * (c * (m x) + d) = a * (m x) + b := by 
      have eq14' : x = (a * (m x) + b) / (c * (m x) + d) := eq14
      have eq19 : c * (m x) + d ≠ 0 := hx4 
      field_simp [eq19] at eq14' ⊢
      nlinarith [eq14']
    -- From m(x) = (a * x +b ) / (c * x +d ) cross multiply
    have eq16 : m x * (c * x + d) = a * x + b := by 
      have eq11' : m x = (a * x + b) / (c * x + d) := eq11 
      have eq18 : c * x + d ≠ 0 := hx3
      field_simp [eq18] at eq11' ⊢
      nlinarith [eq11']
    -- Subtract equations.
    have eq17 : (x - m x) * (a + d) = 0 := by
      have eq18 : x * (c * (m x) + d) = a * (m x) + b := eq15
      have eq19 : m x * (c * x + d) = a * x + b := eq16
      have h20 : (x - m x) * (a + d) = 0 := by
        nlinarith [sq_nonneg (x - m x), sq_nonneg (c * x), sq_nonneg (c * m x), sq_nonneg (c * (x - m x)), sq_pos_of_ne_zero (show c * x + d ≠ 0 by exact hx3), sq_pos_of_ne_zero (show c * (m x) + d ≠ 0 by exact hx4)]
      linarith 
    have eq18 : (x - m x) * (a + d) = 0 := eq17 
    have h21 : a + d = 0 := by
      cases (mul_eq_zero.mp eq18 ) with
      | inl h =>
        -- x - m x = 0, so x = m x. But hx2 : x ≠ m x.
        exfalso
        apply hx2
        linarith [h] 
      | inr h =>
        -- a +d =0
        linarith 
    linarith [ht, h21] 
  · -- Show 0 is in the set.
    intro h0 
    rw [h0] 
    use 1, 0, 0, -1, fun x ↦ -x, 1 
    constructor 
    · -- Show (c ≠ 0 ∨ d ≠ 0)
      norm_num 
    constructor
    · -- Show t = a + d
      norm_num 
    constructor 
    · -- Show m = fun x ↦ (a * x + b) / (c * x + d)
      funext y 
      simp 
      <;> field_simp 
      <;> ring 
    constructor 
    · -- Show x = m (m x)
      norm_num 
    constructor 
    · -- Show x ≠ m x
      norm_num 
    constructor 
    · -- Show c * x + d ≠ 0
      norm_num 
    · -- Show c * m x + d ≠ 0
      norm_num