import Mathlib

open Real Set
open scoped BigOperators

/- 9.209. $\left\{\begin{array}{l}\frac{x^{2}+4}{x^{2}-16 x+64}>0 \\ \lg \sqrt{x+7}>\lg (x-5)-2 \lg 2\end{array}\right.$

The system of inequalities is:
9.209. $\left\{\begin{array}{l}\frac{x^{2}+4}{x^{2}-16 x+64}>0 \\ \lg \sqrt{x+7}>\lg (x-5)-2 \lg 2\end{array}\right.$ -/

lemma l_1 {x : ℝ} (log_defined : 5 < x) (div_defined : x ≠ 8) (hr : ((x - 5) / 2 ^ 2) ^ 2 < x + 7) :
  5 < x ∧ x < 8 ∨ 8 < x ∧ x < 29 := by
  have h1 : ((x - 5) / 2 ^ 2) ^ 2 < x + 7 := hr
  have h2 : 5 < x := log_defined
  have h3 : x ≠ 8 := div_defined

  have h4 : (x - 5) ^ 2 < 16 * (x + 7) := by
    nlinarith

  have h5 : x ^ 2 - 26 * x - 87 < 0 := by
    nlinarith [h4]

  have h6 : -3 < x ∧ x < 29 := by
    constructor
    · -- Prove -3 < x
      nlinarith [show x ^ 2 - 26 * x - 87 < 0 from h5]
    · -- Prove x < 29
      nlinarith [show x ^ 2 - 26 * x - 87 < 0 from h5]

  have h7 : 5 < x := h2
  have h8 : x < 29 := by linarith [h6.right]

  by_cases h9 : x < 8
  · -- Case x < 8
    have h10 : 5 < x := h7
    have h11 : x < 8 := h9
    left
    constructor <;> linarith
  · -- Case x ≥ 8
    push_neg at h9
    have h10 : x > 8 := by
      by_contra h
      push_neg at h
      have h11 : x = 8 := by linarith
      contradiction
    have h12 : x < 29 := h8
    right
    constructor <;> linarith

lemma l_2 {x : ℝ} (log_defined : 5 < x) (div_defined : x ≠ 8) (h : 5 < x ∧ x < 8 ∨ 8 < x ∧ x < 29) :
  0 < (x ^ 2 + 4) / (x ^ 2 - 16 * x + 64) ∧ log (x - 5) - 2 * log 2 < log √(x + 7) := by

  have h1 : 0 < (x ^ 2 + 4) / (x ^ 2 - 16 * x + 64) := by
    have h2 : x ^ 2 + 4 > 0 := by nlinarith [sq_nonneg x]
    have h3 : x ^ 2 - 16 * x + 64 > 0 := by
      have h4 : x ^ 2 - 16 * x + 64 = (x - 8) ^ 2 := by ring
      rw [h4]
      have h5 : (x - 8) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        intro h6
        apply div_defined
        linarith
      linarith
    apply div_pos
    all_goals linarith

  have h2 : log (x - 5) - 2 * log 2 < log √(x + 7) := by
    have h3 : x - 5 > 0 := by linarith
    have h4 : 2 * log 2 = log 4 := by
      rw [← log_rpow]
      norm_num
      all_goals linarith
    have h5 : log (x - 5) - 2 * log 2 = log (x - 5) - log 4 := by
      rw [h4]
    have h6 : log (x - 5) - log 4 = log ((x - 5) / 4) := by
      rw [log_div]
      all_goals linarith
    have h7 : log √(x + 7) = (1 / 2) * log (x + 7) := by
      rw [Real.log_sqrt]
      all_goals linarith
    rw [h5, h6, h7]
    have h8 : (x - 5) / 4 > 0 := by
      nlinarith
    have h9 : x + 7 > 0 := by
      nlinarith
    have h10 : log ((x - 5) / 4) < (1 / 2) * log (x + 7) := by
      have h11 : (x - 5) / 4 > 0 := by
        nlinarith
      have h12 : x + 7 > 0 := by
        nlinarith
      have h13 : ((x - 5) / 4) ^ 2 < x + 7 := by
        cases h with
        | inl h_left =>
          nlinarith
        | inr h_right =>
          nlinarith
      have h14 : log (((x - 5) / 4) ^ 2) < log (x + 7) := by
        apply Real.log_lt_log
        all_goals nlinarith
      have h15 : 2 * log ((x - 5) / 4) = log (((x - 5) / 4) ^ 2) := by
        simp [log_pow]
      linarith [h15, h14]
    linarith [h10]

  exact ⟨h1, h2⟩

theorem inequalities_171335 {x : ℝ} (log_defined : 5 < x) (div_defined: x ≠ 8):
    ((x^2 + 4) / (x^2 - 16 * x + 64) > 0 ∧ log (sqrt (x + 7)) > log (x - 5) - 2 * log 2) ↔
    (5 < x ∧ x < 8 ∨ 8 < x ∧ x < 29) := by

  simp
  constructor
  · rintro ⟨hl, hr⟩
    -- simplify denominator at hl
    rw [show x^2 - 16*x + 64 = (x-8)^2 by ring_nf] at hl
    apply (div_pos_iff_of_pos_right (by refine pow_two_pos_of_ne_zero ?_; intro h; apply div_defined; linarith)).mp at hl
    -- well this makes hl useless
    clear hl
    -- simplify hr
    rw [← Real.log_rpow (by norm_num), ← Real.log_div (by linarith) (by norm_num)] at hr
    apply (Real.log_lt_log_iff (by simp; assumption) (by simp; linarith)).mp at hr
    apply (Real.lt_sqrt (by linarith)).mp at hr
    -- we can now use the lemma l_1
    exact l_1 log_defined div_defined (by norm_cast at hr ⊢)
  · intro h
    -- the other side can be resolved by the lemma l_2
    exact l_2 log_defined div_defined h