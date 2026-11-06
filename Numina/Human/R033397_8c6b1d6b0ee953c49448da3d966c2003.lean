import Mathlib

open Real Set

/- Let $a$ and $b$ be positive real numbers.  Find the minimum value of
\[a^2 + b^2 + \frac{1}{(a + b)^2}.\] -/
theorem algebra_11987 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2 + b^2 + 1 / (a + b)^2 ≥ sqrt 2 ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a^2 + b^2 + 1 / (a + b)^2 = sqrt 2 := by
  -- let s=a+b
  let s := a+b
  have s_def: s = a+b := rfl
  -- a>0,b>0, so a+b ≠ 0
  have snz: s ≠ 0 := by
    rw [s_def]
    linarith [ha, hb]
  rw [← s_def]
  -- notice that (a-b)^2 ≥ 0, or a^2+b^2 ≥ 2ab. add (a^2+b^2) to both sides, we get 2(a^2+b^2) ≥ (a+b)^2. or, (a^2+b^2) ≥ (a+b)^2/2. substitute s=a+b, (a^2+b^2) ≥ s^2/2
  have h1: a^2+b^2 ≥ s^2/2 :=
  calc
    a^2+b^2 = (2*a^2+2*b^2)/2 := by ring
    _ = ((a^2-2*a*b+b^2)+(a^2+2*a*b+b^2))/2 := by ring
    _ = ((a-b)^2+(a+b)^2)/2 := by ring
    _ = s^2/2 + (a-b)^2/2 := by rw [s_def]; ring
    _ ≥ s^2/2 := by
      have := sq_nonneg (a-b)
      linarith [this]
  -- thus a^2+b^2+1/s^2 ≥ s^2/2+1/s^2. notice that s^2/2 = (s/√2)^2 and 1/s^2 = (1/s)^2, it has a form of a^2+b^2 ≥ 2ab. therefore s^2/2+1/s^2 ≥ 2 * (s/√2) * (1/s) = √2
  have h2: s^2/2 + 1/s^2 ≥ √2 :=
  calc
    s^2/2 + 1/s^2 = (s/√2)^2 + (1/s)^2 := by field_simp
    _ = (s/√2)^2 - 2*(s/√2)*(1/s) + (1/s)^2 + 2*(s/√2)*(1/s) := by ring
    _ = ((s/√2)-(1/s))^2 + 2*(s/√2)*(1/s) := by ring
    _ = ((s/√2)-(1/s))^2 + √2 := by
      have: s/√2*(1/s) = 1/√2 := by
        field_simp [snz]; ring
      rw [mul_assoc, this]; field_simp
    _ ≥ √2 := by
      have := sq_nonneg ((s/√2)-(1/s))
      linarith [this]
  constructor
  -- combine h1 and h2, a^2+b^2+1/s^2 ≥ s^2/2+1/s^2 ≥ √2
  · apply le_add_of_le_add_right h2 h1
  -- to verify a^2+b^2+1/s^2 can be √2, notice that in h1, we use (a-b)^2/2 ≥ 0, so a=b is needed. and in h2, we use ((s/√2)-(1/s))^2 ≥ 0, so we have s/√2 = 1/s, solve hte equation, s = √(√2), or a+b = √(√2). so here we should use a=b=√(√2)/2
  · use (√(√2))/2
    use (√(√2))/2
    simp; field_simp; ring_nf; simp; ring