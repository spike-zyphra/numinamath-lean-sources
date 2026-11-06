import Mathlib

namespace algebra_137117

def CubicEq (w : ℂ) := w ^ 3 - 3 * w ^ 2 + 3 * w - 1 = 0
lemma vieta_cubic_eq : ∀ x y z, x + y + z = 3 → x ^ 2 + y ^ 2 + z ^ 2 = 3 → x ^ 3 + y ^ 3 + z ^ 3 = 3 → x * y * z = 1 → CubicEq x ∧ CubicEq y ∧ CubicEq z := by
  sorry

-- 2nd USAMO 1973 Problem 4 Find all complex numbers x, y, z which satisfy x + y + z = x 2 + y 2 + z 2 = x 3 + y 3 + z 3 = 3. Solution
theorem algebra_137117 (x y z : ℂ) :
  x + y + z = 3 ∧ x^2 + y^2 + z^2 = 3 ∧ x^3 + y^3 + z^3 = 3 ↔ (x, y, z) = (1, 1, 1) := by
  constructor
  . rintro ⟨linear_eq, square_sum_eq, cubic_sum_eq⟩
    -- : 1, 1, 1. We have (x + y + z) 2 = (x 2 + y 2 + z 2 ) + 2(xy + yz + zx), so xy + yz + zx = 3.
    have : (x + y + z) ^ 2 = (x ^ 2 + y ^ 2 + z ^ 2) + 2 * (x * y + y * z + z * x) := by
      ring
    have x_y_sum_eq : x * y + y * z + z * x = 3 := by
      rw [linear_eq, square_sum_eq] at this
      norm_num at this
      have := congrArg (fun x => (x - 3) / 2) this
      norm_num at this
      exact this.symm
    -- (x + y + z) 3 = (x 3 + y 3 + z 3 ) + 3(x 2 y + xy 2 + y 2 z + yz 2 + z 2 x + zx 2 ) + 6xyz, so 8 = (x 2 y + xy 2 + y 2 z + yz 2 + z 2 x + zx 2 ) + 2xyz.
    have : (x + y + z) ^ 3 = (x ^ 3 + y ^ 3 + z ^ 3) + 3 * (x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2) + 6 * (x * y * z) := by
      ring
    have eq₂ : 8 = (x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2) + 2 * (x * y * z) := by
      rw [linear_eq, cubic_sum_eq] at this
      norm_num at this
      --linarith
      generalize h : x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2 = a
      rw [h] at this
      generalize h : x * y * z = b
      rw [h] at this
      --linarith
      rw [show 3 + 3 * a + 6 * b = 3 + 3 * (a + 2 * b) by ring] at this
      generalize h : a + 2 * b = c
      rw [h] at this
      --linarith
      convert congrArg (fun x => (x - 3) / 3) this
      . norm_num
      . simp
    -- But (x + y + z)(xy + yz + zx) = (x 2 y + xy 2 + y 2 z + yz 2 + z 2 x + zx 2 ) + 3xyz, so xyz = -1.
    -- It should be "xyz = 1". The is a mistake in the solution statement above.
    have : (x + y + z) * (x * y + y * z + z * x) = (x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2) + 3 * (x * y * z) := by
      ring
    have : x * y * z = 1 := by
      rw [show (x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2) + 3 * (x * y * z) =
        (x ^ 2 * y + x * y ^ 2 + y ^ 2 * z + y * z ^ 2 + z ^ 2 * x + z * x ^ 2) + 2 * (x * y * z) + (x * y * z) by ring
      ] at this
      rw [linear_eq, x_y_sum_eq, ←eq₂] at this
      norm_num at this
      have := congrArg (fun x => x - 8) this
      norm_num at this
      exact this.symm
    -- Hence x, y, z are the roots of the cubic w 3 - 3w 2 + 3w - 1 = (w - 1) 3 .
    let CubicEq (w : ℂ) := w ^ 3 - 3 * w ^ 2 + 3 * w - 1 = 0
    have := vieta_cubic_eq x y z linear_eq square_sum_eq cubic_sum_eq this
    rcases this with ⟨cubic_eq_x, cubic_eq_y, cubic_eq_z⟩
    -- Hence x = y = z = 1.
    have : CubicEq = fun w => (w - 1) ^ 3 = 0 := by
      ext w
      unfold CubicEq
      ring_nf
    simp
    have solve {w} (cubic_eq_w : CubicEq w) : w = 1 := by
      rw [this] at cubic_eq_w
      simp at cubic_eq_w
      have := congrArg (. + 1) cubic_eq_w
      norm_num at this
      exact this
    constructor
    . exact solve cubic_eq_x
    constructor
    . exact solve cubic_eq_y
    . exact solve cubic_eq_z
    -- 2nd USAMO 1973 © John Scholes jscholes@kalva.demon.co.uk 11 May 2002
  . rintro ⟨rfl, rfl, rfl⟩
    norm_num

end algebra_137117
open algebra_137117
