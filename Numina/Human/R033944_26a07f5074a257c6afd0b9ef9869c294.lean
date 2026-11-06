import Mathlib

/- The positive integers $\mathrm{a}, \mathrm{b}, \mathrm{c}, \mathrm{d}, \mathrm{p}, \mathrm{q}$ satisfy $\mathrm{ad}-\mathrm{bc}=1 \mathrm{and} \mathrm{a} / \mathrm{b}>\mathrm{p} / \mathrm{q}>\mathrm{c} / \mathrm{d}$. Show that $\mathrm{q}>=\mathrm{b}+$ $d$ and that if $q=b+d$, then $p=a+c$. -/
theorem number_theory_604212
    (a b c d p q : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (hp : 0 < p)
    (hq : 0 < q)
    (h1 : a * d - b * c = 1)
    (h2 : (a : ℝ) / b > (p : ℝ) / q)
    (h3 : (p : ℝ) / q > (c : ℝ) / d) :
    q ≥ b + d ∧ (q = b + d → p = a + c) := by
  -- We can rewrite the conditions as:
  -- p * d ≥ c * q + 1
  -- a * q ≥ p * b + 1
  rw [gt_iff_lt, div_lt_div_iff₀ (Int.cast_pos.mpr hd) (Int.cast_pos.mpr hq)] at h3
  norm_cast at h3
  change p * d ≥ c * q + 1 at h3
  rw [gt_iff_lt, div_lt_div_iff₀ (Int.cast_pos.mpr hq) (Int.cast_pos.mpr hb)] at h2
  norm_cast at h2
  change a * q ≥ p * b + 1 at h2
  constructor
  . -- For the first part, we calculate:
    calc
      q = q * (a * d - b * c) := by simp [h1]
      _ = d * (a * q) - b * (c * q) := by ring
      _ ≥ d * (p * b + 1) - b * (p * d - 1) := by nlinarith only [hd, h3, hb, h2]
      _ = b + d := by ring
  . intro h
    -- It suffices to show both p ≤ a + c and p ≥ a + c.
    apply le_antisymm
    . -- Add a * b to both sides of h1
      have h4 : (a + c) * b ≥ a * (b + d) - 1 := by nlinarith only [h1, hb]
      rw [← h] at h4
      replace h4 : (a + c) * b ≥ p * b := by linarith only [h2, h4]
      exact le_of_mul_le_mul_right h4 hb
    . -- Add c * d to both sides of h1
      have h4 : (a + c) * d ≤ c * (b + d) + 1 := by nlinarith only [h1, hd]
      rw [← h] at h4
      exact le_of_mul_le_mul_right (le_trans h4 h3) hd
