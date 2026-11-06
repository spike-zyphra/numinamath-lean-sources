import Mathlib

/- If $a$, $b$, and $c$ are integers satisfying $a + \frac 1b = \frac{22}{7}$, $b + \frac 1c = 8$, and $abc = 21$, then find $c + \frac 1a$. Express your answer as a common fraction. -/
theorem algebra_20650 {a b c : ℝ} (h₀ : a + 1 / b = 22 / 7) (h₁ : b + 1 / c = 8) (h₂ : a * b * c = 21)
  (hz: ∃(az bz cz:ℤ), az = a ∧ bz = b ∧ cz = c) :
    c + 1 / a = 4 / 3 := by
  -- abc = 21 ≠ 0, obviously, a,b,c all nonzero
  have anz: a ≠ 0 := by
    by_contra!; rw [this] at h₂; simp at h₂
  have bnz: b ≠ 0 := by
    by_contra!; rw [this] at h₂; simp at h₂
  have cnz: c ≠ 0 := by
    by_contra!; rw [this] at h₂; simp at h₂
  -- notice that (a+1/b)(b+1/c)(c+1/a) = abc+(a+1/b)+(b+1/c)+(c+1/a)+1/(abc)
  have h1: (a+1/b)*(b+1/c)*(c+1/a) = a*b*c + (a+1/b) +
    (b+1/c) + (c+1/a) + 1/(a*b*c) := by
    ring_nf
    field_simp [anz,bnz,cnz]
    ring
  -- therefore we can determine c+1/a
  let x := c+1/a
  have x_def: x = c+1/a := rfl
  rw [h₀, h₁, h₂, ← x_def] at h1
  -- now we have 22/7 * 8 * x = 21 + 22/7 + 8 + x + 1/21. simplify, we have the following.
  have h2: (22/7*8-1)*x = 21+22/7+8+1/21 := by
    rw [sub_mul, h1]; ring
  -- left side, 22/7x8-1 = 169/7. and right side, 29+67/21 = 676/21
  have h3: (169/7)*x = 676/21 := by
    have hh1: 22/7*8-(1:ℝ) = 169/7 := by ring
    have hh2: 21+22/7+(8:ℝ)+1/21 = 676/21 := by ring
    rwa [hh1, hh2] at h2
  -- 169/7 = 507/21, so x = 676/507
  have h4: x = 676/507 := by
    have: x = 169/7 * x * (21/507) := by ring
    rw [this, h3]; ring
  -- 676 = 4x169, 507 = 3x169, so x=4/3, or c+1/a = 4/3
  rw [← x_def, h4]; norm_num