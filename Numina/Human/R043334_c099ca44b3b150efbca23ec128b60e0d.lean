import Mathlib

open Real Set

/- II. (50 points)
Given that $x, y, z$ are all positive real numbers, find the minimum value of $\iota=\frac{(x+y-z)^{2}}{(x+y)^{2}+z^{2}}+\frac{(z+x-y)^{2}}{(z+x)^{2}+y^{2}}+\frac{(y+z-x)^{2}}{(y+z)^{2}+x^{2}}$. -/
theorem inequalities_221983 : IsLeast {((x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2)) +
      ((z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2)) +
      ((y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2)) | (x : ℝ) (y : ℝ) (z : ℝ)
      (_ : 0 < x) (_ : 0 < y) (_ : 0 < z)} (3/5) := by
  constructor
  -- first we prove that using 1, 1, 1 we get minimum value
  . use 1, 1, 1, by norm_num, by norm_num, by norm_num
    norm_num
  -- to prove 3/5 is a lower bound, first we prove following lemma
  . have aux {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc: 0 < c) :
        c * (a + b) / ((a + b)^2 + c^2) ≤ 2/5 - 9 * (a + b - 2 * c) / (25 * (a + b + c)) := by
      suffices 9 * (a + b - 2 * c) / (25 * (a + b + c)) ≤ 2 / 5 - c * (a + b) / ((a + b)^2 + c^2) by linarith
      have : 2/5 - c * (a + b) / ((a + b)^2 + c^2) = (a + b - 2*c) * (2*a + 2*b - c) / (5 * ((a + b)^2 + c^2)) := by
        field_simp
        ring
      rw [this]
      apply div_le_div_iff₀ (by positivity) (by positivity) |>.mpr
      -- the full expression boils down to following, which is nonnegative
      have : 0 ≤ (a + b - 2 * c)^2 * (a + b + 7*c) := by positivity
      linear_combination 5 * this
    -- we prove another lemma that the terms in goal can be related to terms in our previous lemma
    have aux' {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc: 0 < c) :
        (a + b - c)^2 / ((a + b)^2 + c^2) = 1 - 2 * c * (a + b) / ((a + b)^2 + c^2) := by
      field_simp
      ring
    -- now we can prove the goal, have the aux applied to triples of x, y, z
    rintro t h
    obtain ⟨x, y, z, hx, hy, hz, ht⟩ := h
    rw [← ht]
    have h₁ := aux hx hy hz
    have h₂ := aux hy hz hx
    have h₃ := aux hz hx hy
    -- prove that the 3 terms summed from them result to 0
    have h : 9 * (x + y - 2 * z) / (25 * (x + y + z)) + 9 * (y + z - 2 * x) / (25 * (y + z + x))
        + 9 * (z + x - 2 * y) / (25 * (z + x + y)) = 0 := by
      field_simp
      ring
    -- then add up the 3 inequalities
    replace h : z * (x + y) / ((x + y) ^ 2 + z ^ 2) + x * (y + z) / ((y + z) ^ 2 + x ^ 2)
        + y * (z + x) / ((z + x) ^ 2 + y ^ 2) ≤ 6/5 := by linarith
    -- use the second lemma and our goal is twice the previous inequality
    rw [aux' hx hy hz, aux' hy hz hx, aux' hz hx hy]
    linear_combination 2 * h