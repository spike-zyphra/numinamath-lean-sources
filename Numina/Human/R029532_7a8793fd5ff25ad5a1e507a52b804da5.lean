import Mathlib

/- 3. For real numbers $a$ and $b$, it holds that $a^{3}=3 a b^{2}+11$ and $b^{3}=3 a^{2} b+2$. Calculate the value of the expression $a^{2}+b^{2}$. -/
theorem algebra_129607 {a b : ℝ} (ha : a^3 = 3 * a * b^2 + 11) (hb : b^3 = 3 * a^2 * b + 2) :
    a^2 + b^2 = 5 := by
  -- Cube both sides of the goal.
  rw [← pow_left_inj₀ (by positivity) (by norm_num) (show 3 ≠ 0 by norm_num)]
  -- The new goal is (a^2 + b^2)^3 = 5^3. It can be solved directly with polyrith.
  -- Consider a more detailed proof.
  calc
    -- We have (a^2 + b^2) ^ 3 = (a ^ 3 - 3 * a * b)^2 + (b ^ 3 - 3 * a^2 * b)^2
    (a^2 + b^2) ^ 3 = (a ^ 3 - 3 * a * b^2)^2 + (b ^ 3 - 3 * a^2 * b)^2 := by ring
    -- a ^ 3 - 3 * a * b = 11 from ha and
    -- b ^ 3 - 3 * a^2 * b from hb.
    _ = 11^2 + 2^2 := by congr <;> linarith
    _ = 5^3 := by norm_num