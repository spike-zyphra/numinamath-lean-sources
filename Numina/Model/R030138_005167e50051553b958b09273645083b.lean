import Mathlib

theorem algebra_3568
    (a b c d : ℝ)
    (h₀ : a ≠ b)
    (h₁ : a ≠ c)
    (h₂ : a ≠ d)
    (h₃ : b ≠ c)
    (h₄ : b ≠ d)
    (h₅ : c ≠ d)
    (h₆ : (a ^ 2 - 10 * c * a - 11 * d) = 0)
    (h₇ : (b ^ 2 - 10 * c * b - 11 * d) = 0)
    (h₈ : (c ^ 2 - 10 * a * c - 11 * b) = 0)
    (h₉ : (d ^ 2 - 10 * a * d - 11 * b) = 0) :
    a + b + c + d = 1210 := by
  have eq1 : a + b = 10 * c := by
    have h10 : a ^ 2 - b ^ 2 = 10 * c * (a - b) := by
      nlinarith
    have h11 : a + b = 10 * c := by
      apply (mul_left_inj' (sub_ne_zero.mpr h₀)).mp
      linarith
    linarith
  have eq2 : c + d = 10 * a := by
    have h10 : c ^ 2 - d ^ 2 = 10 * a * (c - d) := by
      nlinarith
    have h11 : c + d = 10 * a := by
      apply (mul_left_inj' (sub_ne_zero.mpr h₅)).mp
      linarith
    linarith
  have eq3 : b = 10 * c - a := by
    linarith [eq1]
  have eq4 : d = 10 * a - c := by
    linarith [eq2]
  -- Express all variables in terms of a and c.
  -- Now from h₆, h₇, h₈, h₉.
  -- Let's substitute b and d in terms of a and c.
  -- From h₆: a ^ 2 - 10 * c * a - 11 * d = 0
  have eq6 : a ^ 2 - 10 * a * c - 110 * a + 11 * c = 0 := by 
    rw [show d = 10 * a - c by linarith [eq4] ] at h₆
    linarith
  -- From h₈: c ^ 2 - 10 * a * c - 11 * b = 0
  have eq7 : c ^ 2 - 10 * a * c + 11 * a - 110 * c = 0 := by
    rw [show b = 10 * c - a by linarith [eq3] ] at h₈
    linarith
  have eq51 : a ^ 2 - c ^ 2 - 121 * (a - c) = 0 := by
    nlinarith [eq6, eq7]
  have eq52 : (a - c) * (a + c - 121) = 0 := by
    nlinarith [eq51]
  cases' (mul_eq_zero.mp eq52) with h53 h54
  · -- a -c =0 
    have h54 : a = c := by linarith
    tauto
  · -- a +c =121 
    have h9 : a + c = 121 := by linarith [h54]
    -- total sum a +b +c +d 
    have eq5 : a + b + c + d = 10 * (a + c) := by
      nlinarith [eq1, eq2]
    have eq53 : a + b + c + d = 1210 := by
      nlinarith [eq5, h9]
    linarith [eq53]