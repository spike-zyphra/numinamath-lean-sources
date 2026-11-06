import Mathlib

open Real

/- Determine the smallest number $M$ such that the inequality  $$ \left|a b\left(a^{2}-b^{2}\right)+b c\left(b^{2}-c^{2}\right)+c a\left(c^{2}-a^{2}\right)\right| \leq M\left(a^{2}+b^{2}+c^{2}\right)^{2} $$  holds for all real numbers $a, b, c$.  (Ireland) -/
theorem algebra_23542 (M : ℝ) :
    (∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
          M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ↔
      9 * sqrt 2 / 32 ≤ M := by
  constructor
  · intro h
    set α := sqrt (2:ℝ)
    have hα : α ^ 2 = 2 := sq_sqrt (by norm_num)
    let a := 2 - 3 * α
    let c := 2 + 3 * α
    calc _ = 18 ^ 2 * 2 * α / 48 ^ 2 := by ring
      _ ≤ M := ?_
    rw [div_le_iff₀ (by positivity)]
    calc 18 ^ 2 * 2 * α
        = 18 ^ 2 * α ^ 2 * α := by linear_combination -324 * α * hα
      _ = abs (-(18 ^ 2 * α ^ 2 * α)) := by rw [abs_neg, abs_of_nonneg]; positivity
      _ = |a * 2 * (a ^ 2 - 2 ^ 2) + 2 * c * (2 ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| := by ring_nf!
      _ ≤ M * (a ^ 2 + 2 ^ 2 + c ^ 2) ^ 2 := by apply h
      _ = M * 48 ^ 2 := by linear_combination (324 * α ^ 2 + 1080) * M * hα
  · intro h a b c
    have h1 : |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
      9 * sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
      -- Let $x = a - b$，$y = b - c$，$z = c - a$，$s = a + b + c$. Then we want to have \[ |xyzs| \leq \frac{M}{9}(x^2 + y^2 + z^2 + s^2)^2. \]. Here $x + y + z = 0$
      have h11 (x y z s : ℝ) (hxyz : x + y + z = 0) :
        |x * y * z * s| ≤ sqrt 2 / 32 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by
        wlog h' : 0 ≤ x * y generalizing x y z; swap
        · rw [div_mul_eq_mul_div, le_div_iff₀' (by norm_num)]
          have hz : (x + y) ^ 2 = z ^ 2 := by linear_combination (x + y - z) * hxyz
          have this :=
            calc
              2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)
                ≤ _ * _ ^ 3 := by
                gcongr
                have : (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y)) ≥ 0 := by positivity
                calc 16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 2 * (x + y) ^ 2 := by gcongr; linarith
                  _ = ((x + y) ^ 2) ^ 3 := by ring
              _ ≤ (3 * (x + y) ^ 2 + 2 * s ^ 2) ^ 4 / 4 ^ 4 := by
                rw [le_div_iff₀ (by norm_num)]
                have : 0 ≤ (2 * s ^ 2 - (x + y) ^ 2) ^ 2 * ((2 * s ^ 2 + 7 * (x + y) ^ 2) ^ 2 +
                  2 * (4 * (x + y) ^ 2) ^ 2) := by positivity
                linarith
              _ ≤ (2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4 := by
                  gcongr (?_ + _) ^ 4 / _
                  linarith [sq_nonneg (x - y)]
          refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
          calc
            (32 * |x * y * z * s|) ^ 2 = 32 * (2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)) := by
              rw [mul_pow, sq_abs, hz]; ring
            _ ≤ 32 * ((2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4) := by gcongr
            _ = (sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2) ^ 2 := by
              field_simp
              rw [mul_pow, sq_sqrt zero_le_two, hz]
              ring
        rcases (mul_nonneg_of_three x y z).resolve_left h' with h | h
        · convert this y z x _ h using 2 <;> linarith
        · convert this z x y _ h using 2 <;> linarith
      -- It's the same as $|(a - b)(b - c)(c - a)(a + b + c)| \leq M \left(a^2 + b^2 + c^2\right)^2$.
      calc
        _ = |(a - b) * (b - c) * (c - a) * -(a + b + c)| := by ring_nf
        _ ≤ _ := h11 (a - b) (b - c) (c - a) (-(a + b + c)) (by ring)
        _ = _ := by ring
    exact h1.trans (by gcongr)