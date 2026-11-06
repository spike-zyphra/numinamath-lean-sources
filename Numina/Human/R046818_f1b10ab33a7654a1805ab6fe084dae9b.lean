import Mathlib

open Real Set

/- Determine the maximum of the expression


$$

x^{2} y+y^{2} z+z^{2} x-x^{2} z-y^{2} x-z^{2} y

$$


for $0 \leqslant x \leqslant 1,0 \leqslant y \leqslant 1,0 \leqslant z \leqslant 1$. -/
theorem algebra_113478 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧ t = x^2 * y + y^2 * z + z^2 * x - x^2 * z - y^2 * x - z^2 * y} (1/4) := by
  constructor
    -- show 1/4 is in the set by using 1, 1/2, 0 for x, y, z
  . use 1, 1/2, 0
    and_intros
    all_goals norm_num
    -- to show the upper boundness, convert the expression to (x-y) * (x-z) * (y-z) via ring
  . rintro t ⟨x, y, z, hx, hy, hz, ht⟩
    rw [ht]
    convert_to (x - y) * (x - z) * (y - z) ≤ 1/4
    . ring
    -- next prove a specific version where for a, b, c; a >= b, c
    have gen {a b c : ℝ} (ha: a ∈ Icc 0 1) (hc : c ∈ Icc 0 1) (hab: b ≤ a) (hac: c ≤ a) : (a - b) * (a - c) * (b - c) ≤ 1 / 4 := by
      clear * - hab hac ha hc
      -- use am-gm on (a-b), (b-c) to make it (a-c)^3/4, which is less than 1^3/4
      calc
        (a-b)*(a-c)*(b-c) = (a-c) * ((a-b) * (b-c)) := by ring
        _ ≤ (a-c) * (((a-b) + (b-c))/ 2)^2 := by
          gcongr
          linarith
          linarith [show 0 ≤ ((a-b) - (b-c))^2 by positivity]
        _ = (a-c)^3 / 4 := by ring
        _ ≤ (1-0)^3 / 4 := by
          gcongr
          all_goals linarith [ha.right, hc.left]
        _ = 1 / 4 := by norm_num
    -- now use case work to bring 3 cases, where x is largest, where y is largest, where z is largest. in each case apply the specific version
    by_cases hx_bounds : y ≤ x ∧ z ≤ x
    . exact gen hx hz hx_bounds.left hx_bounds.right
    push_neg at hx_bounds
    by_cases hyz : z ≤ y
    . have hxy : x ≤ y := by
        by_contra
        linarith [hx_bounds (by linarith)]
      convert gen hy hx hyz hxy using 1
      ring
    . have hyz : y ≤ z := by linarith
      have hxy : x ≤ z := by
        by_contra
        linarith [hx_bounds (by linarith)]
      convert gen hz hy hxy hyz using 1
      ring