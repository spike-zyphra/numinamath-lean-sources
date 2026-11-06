import Mathlib

/- Given that the third term of a geometric sequence is $1053$ and the ninth term is $\frac{13}{9}$, find the value of the seventh term. -/
theorem algebra_18597 {a r : ℚ} (hr : r ≠ 0) (h3 : a * r^2 = 1053) (h9 : a * r^8 = 13 / 9) :
    a * r^6 = 13 := by
  -- since it's a geometric sequence, suppose it is a, ar, ar^2, ar^3,...
  -- given third term and ninth term, we can solve r.
  have hh1: r^6 = (a*r^8) / (a*r^2) := by
    field_simp [hr]; ring
  have hh2: r = 1/3 ∨ r = -1/3 := by
    rw [h3, h9] at hh1
    -- 1053 = 13x81 = 13 x 3^4
    have: (13/9/1053:ℚ) = (1/3)^6 := by norm_num
    rw [this] at hh1
    rw [pow_eq_pow_iff_cases] at hh1
    rcases hh1 with ht1 | ht2 | ht3
    · norm_num at ht1
    · tauto
    · rw [ht3.left]; right; norm_num
  -- given r, the seventh term is ar^6 = (ar^2)*r^4, so it suffices to calculate r^4 and substitute in.
  have hh3: r^4 = 1/81 := by
    rcases hh2 with hhr | hhr
    <;> rw [hhr] <;> norm_num
  have hh4: a*r^6 = (a*r^2)*r^4 := by ring
  rw [hh4, h3, hh3]
  -- 1053 /81 = 13
  norm_num