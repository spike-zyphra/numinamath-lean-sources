import Mathlib

/-
5. The numbers $\frac{1}{a+b}, \frac{1}{a+c}, \frac{1}{b+c}$ form an arithmetic progression.

Is it true that the numbers $a^{2}, b^{2}, c^{2}$ also form an arithmetic progression?
-/
theorem algebra_111255 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : a ≠ -c)
    (h : ∃ d, 1 / (a + b) = 1 / (a + c) + d ∧ 1 / (a + c) = 1 / (b + c) + d) :
    ∃ d, a ^ 2 = b ^ 2 + d ∧ b ^ 2 = c ^ 2 + d := by
  rcases h with ⟨d, h1, h2⟩
  have h3 : a + b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h4 : a + c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h5 : b + c ≠ 0 := by
    intro h
    apply hb
    linarith
  have eq1 : 1 / (a + b) + 1 / (b + c) = 2 * (1 / (a + c)) := by
    have h2' : d = 1 / (a + c) - 1 / (b + c) := by linarith
    have h1' : 1 / (a + b) = 1 / (a + c) + d := h1
    rw [h2'] at h1'
    linarith
  have h_eq : a ^ 2 + c ^ 2 = 2 * b ^ 2 := by
    have eq1' : 1 / (a + b) + 1 / (b + c) = 2 * (1 / (a + c)) := eq1
    have eq2 : a + c ≠ 0 := by assumption
    have eq3 : a + b ≠ 0 := by assumption
    have eq4 : b + c ≠ 0 := by assumption
    field_simp at eq1'
    nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (a + c),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  use a ^ 2 - b ^ 2
  constructor
  · -- a^2 = b^2 + (a^2 - b^2)
    ring
  · -- b^2 = c^2 + (a^2 - b^2)
    nlinarith [h_eq]
