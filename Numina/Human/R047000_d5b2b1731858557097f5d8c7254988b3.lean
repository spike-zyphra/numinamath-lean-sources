import Mathlib

open Real

/- 1. If the function $f(x)=\log _{a}\left(x+\sqrt{b x^{2}+2 a^{2}}\right) \quad(a>0$ and $a \neq-1)$ is an odd function, then the real number pair $(a, b)=$ $\qquad$ . -/
theorem algebra_284580 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1)
    (hab : ∀ x, b * x ^ 2 + 2 * a ^ 2 > x ^ 2)
    (f : ℝ → ℝ) (hf : f = λ x => logb a (x + sqrt (b * x ^ 2 + 2 * a ^ 2)))
    (hodd : ∀ x, f (-x) = -f x) :
    a = sqrt 2 / 2 ∧ b = 1 := by
  replace hf x : f x = logb a (x + √(b * x ^ 2 + 2 * a ^ 2)) := by simp [hf]
  -- f(0) = 0 because f is odd.
  have hf0 : f 0 = 0 := by
    have h := hodd 0
    simp at h
    linarith
  -- Show that a = √2 / 2.
  have ha_eq : a = √2 / 2 := by
    suffices a = √2 / 2 ↔ True by simp only [this]
    calc
      -- We have a = √2 / 2 iff logb a (a * √2) = 0.
      a = √2 / 2 ↔ logb a (a * √2) = 0 := by
        have h : a * √2 ≠ -1 := by
          suffices 0 < a * √2 by linarith
          apply mul_pos (by linarith) (by positivity)
        -- logb a (a * √2) = 0 iff a * √2 = 1.
        simp [logb_eq_zero, ha, show a ≠ 0 ∧ a ≠ -1 by constructor <;> linarith, h]
        -- a * √2 = 1 ↔ a = 1 / √2 = √2 / 2.
        rw [show √2 / 2 = 1 / √2 by field_simp]
        field_simp
      -- logb a (a * √2) = f(0)
      _ ↔ f 0 = 0 := by
        rw [hf 0, zero_pow (by norm_num), mul_zero, zero_add, zero_add]
        rw [sqrt_mul (by norm_num), sqrt_sq (by linarith), mul_comm]
      _ ↔ True := by simp [hf0]
  simp [ha_eq]
  -- Show that logb a ((b - 1) * x^2 + 1) = 0 for all x.
  have hb0 : ∀ x, logb a ((b - 1) * x ^ 2 + 1) = 0 := by
    intro x
    symm
    calc
      -- We have f(x) + f(-x) = 0 because f is odd.
      0 = f x + f (-x) := by simp [hodd]
      -- f(x) + f(-x) = logb a ((x + √(b * x ^ 2 + 2 * a^2)) * (-x + √(b * x ^ 2 + 2 * a^2))).
      _ = logb a ((x + √(b * x ^ 2 + 2 * a^2)) * (-x + √(b * x ^ 2 + 2 * a^2))) := by
        simp_rw [hf, neg_pow_two]
        have ineq : |x| < √(b * x^2 + 2 * a^2) := calc
          |x| = √(x ^ 2) := by rw [sqrt_sq_eq_abs]
          _ < √(b * x^2 + 2 * a^2) := by apply sqrt_lt_sqrt (by positivity) (hab x)
        rw [← logb_mul]
        · suffices -x ≤ |-x| by simp at this; linarith
          exact le_abs_self _
        · linarith [le_abs_self x]
      -- Simplify the expression and get
      -- logb a (b * x ^ 2 + 2 * a ^ 2 - x ^ 2).
      _ = logb a (b * x ^ 2 + 2 * a ^ 2 - x ^ 2) := by
        congr
        ring_nf
        rw [sq_sqrt (by nlinarith [hab x])]
        ring
      -- The result follows from 2 * a ^ 2 = 1.
      _ = logb a ((b - 1) * x ^ 2 + 1) := by
        suffices 2 * a ^ 2 = 1 by rw [this]; ring_nf
        rw [ha_eq, div_pow, sq_sqrt (by norm_num)]
        norm_num
  -- logb a ((b - 1) * x^2 + 1) = 0 iff (b - 1) * x^2 + 1 ∈ {-1, 0, 1} for all x.
  simp [logb_eq_zero, ha, show a ≠ 0 ∧ a ≠ -1 by constructor <;> linarith] at hb0
  -- Consider x = 1.
  rcases hb0 1 with h | h | h
  -- Assume that (b - 1) * 1 + 1 = 0. Then b = 0.
  · replace h : b = 0 := by linarith
    simp [h] at hb0
    -- Now consider x = 2. We get -4 + 1 ∈ {-1, 0, 1}, a contradiction.
    have := hb0 2
    norm_num at this
  -- Assume that (b - 1) * 1 + 1 = 1. Then b = 1 and the result follows.
  · simp at h
    linarith
  -- Assume that (b - 1) * 1 + 1 = -1. Then b = -1.
  · replace h : b = -1 := by linarith
    simp [h] at hb0
    -- Consider x = 2. We get -8 + 1 ∈ {-1, 0, 1}, a contradiction.
    have := hb0 2
    norm_num at this