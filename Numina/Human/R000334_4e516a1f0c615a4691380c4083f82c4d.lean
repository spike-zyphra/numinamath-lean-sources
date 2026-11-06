import Mathlib
import Aesop

open BigOperators Real Topology Rat

/- Determine all integers  $x$  satisfying
\[ \left[\frac{x}{2}\right] \left[\frac{x}{3}\right] \left[\frac{x}{4}\right] = x^2. \]
( $[y]$  is the largest integer which is not larger than  $y.$ )-/
theorem number_theory_8966 (x : ℤ) : ⌊(x : ℝ) / 2⌋ * ⌊(x : ℝ) / 3⌋ * ⌊(x : ℝ) / 4⌋ = (x : ℝ) ^ 2  ↔
    x = 0 ∨ x = 24 := by
  constructor
  swap
  -- Verify that 0 and 24 are solutions.
  . rintro (rfl | rfl) <;> norm_num
  . intro hx
    -- Clearly  $x$  is nonnegative integers because otherwise
    -- \[ \left[\frac{x}{2}\right] \left[\frac{x}{3}\right] \left[\frac{x}{4}\right] \]
    -- will be negative whereas  $x^2$  is nonnegative.
    have hxnonneg : 0 ≤ x := by
      by_contra hxneg
      replace hxneg : x < 0 := Int.lt_of_not_ge hxneg
      have h1 : ⌊(x : ℝ) / 2⌋ < 0 := by
        rify
        apply lt_of_le_of_lt (Int.floor_le ((x : ℝ) / 2))
        suffices (-x : ℝ) / 2 > 0 by linarith
        exact half_pos (by exact_mod_cast Int.neg_pos_of_neg hxneg)
      have h2 : ⌊(x : ℝ) / 3⌋ < 0 := by
        rify
        apply lt_of_le_of_lt (Int.floor_le ((x : ℝ) / 3))
        suffices (-x : ℝ) / 2 > 0 by linarith
        exact half_pos (by exact_mod_cast Int.neg_pos_of_neg hxneg)
      have h3 : ⌊(x : ℝ) / 4⌋ < 0 := by
        rify
        apply lt_of_le_of_lt (Int.floor_le ((x : ℝ) / 4))
        suffices (-x : ℝ) / 2 > 0 by linarith
        exact half_pos (by exact_mod_cast Int.neg_pos_of_neg hxneg)
      have := Int.mul_pos_of_neg_of_neg h1 h2
      have := Int.mul_neg_of_pos_of_neg this h3
      rify at this
      rw [hx] at this
      have : 0 ≤ (x : ℝ) ^ 2 := sq_nonneg _
      have : 0 < (0 : ℝ) := by linarith
      linarith
    have h1 := mul_lt_mul_of_pos_right
      (Int.lt_floor_add_one (x / 2 : ℝ))
      (show 0 < (2 : ℝ) by norm_num)
    have h2 := mul_lt_mul_of_pos_right
      (Int.lt_floor_add_one (x / 3 : ℝ))
      (show 0 < (3 : ℝ) by norm_num)
    have h3 := mul_lt_mul_of_pos_right
      (Int.lt_floor_add_one (x / 4 : ℝ))
      (show 0 < (4 : ℝ) by norm_num)
    rw [div_mul_cancel₀ _ (by norm_num)] at h1 h2 h3
    norm_cast at h1 h2 h3
    change x + 1 ≤ _ at h1 h2 h3
    rify at h1 h2 h3
    replace h1 : ((x : ℝ) - 1) / 2 ≤ ⌊(x : ℝ) / 2⌋ := by
      rw [show ⌊(x : ℝ) / 2⌋ = (⌊x /. 2⌋ : ℝ) by norm_cast]
      linarith
    replace h2 : ((x : ℝ) - 2) / 3 ≤ ⌊(x : ℝ) / 3⌋ := by
      rw [show ⌊(x : ℝ) / 3⌋ = (⌊x /. 3⌋ : ℝ) by norm_cast]
      linarith
    replace h3 : ((x : ℝ) - 3) / 4 ≤ ⌊(x : ℝ) / 4⌋ := by
      rw [show ⌊(x : ℝ) / 4⌋ = (⌊x /. 4⌋ : ℝ) by norm_cast]
      linarith
    by_cases hxgt : x > 29
    -- Clearly  $\left[\frac{x}{2}\right] \left[\frac{x}{3}\right] \left[\frac{x}{4}\right]
    -- \geq P=\frac{x-1}{2} \cdot \frac{x-2}{3} \cdot \frac{x-3}{4}$
    -- which is greater than  $x^2$  for all  $x>29$ ,
    . have : 0 < (x : ℝ) - 1 := by norm_cast; omega
      have hx2_nonneg : 0 ≤ ((x : ℝ) - 1) / 2 := by linarith
      have : 0 < (x : ℝ) - 2 := by norm_cast; omega
      have hx3_nonneg : 0 ≤ ((x : ℝ) - 2) / 3 := by linarith
      have : 0 < (x : ℝ) - 3 := by norm_cast; omega
      have hx4_nonneg : 0 ≤ ((x : ℝ) - 3) / 4 := by linarith
      let P (x : ℤ) := (((x : ℝ) - 1) / 2)*(((x : ℝ) - 2) / 3)*(((x : ℝ) - 3) / 4) > x ^ 2
      have hp30 : P 30 := by simp [P]; norm_num
      have hpsucc (x : ℤ) (hn : 30 ≤ x) (hp : P x) : P (x + 1) := by
        simp [P] at hp ⊢
        field_simp at hp ⊢
        rw [lt_div_iff (by norm_num)] at hp ⊢
        norm_cast at hp ⊢
        norm_num at hp ⊢
        have (a b c : ℤ) (hab : a < b) : a + c < b + c := by
          exact (add_lt_add_iff_right c).mpr hab
        rw [← add_lt_add_iff_right (48 * x + 24)] at hp
        trans (x-1)*(x-2)*(x-3) + (48*x+24)
        . convert hp using 1; ring
        rw [← sub_pos]
        ring_nf
        have : 20 ≤ x - 10 := by omega
        have : 20^2 ≤ (x - 10)^2 := by apply pow_le_pow_left (by norm_num) this
        have : 0 < 3*(x - 10)^2 - 318 := by omega
        have : 0 < 3*x^2 - 60*x - 18 := by
          convert this using 1
          ring
        have : 3*x^2 - 60*x - 18 < 3*x^2 - 57*x - 18 := by omega
        omega
      have hpx := Int.le_induction hp30 hpsucc x hxgt
      simp [P] at hpx
      have hmul_le_mul {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) :
          a*c ≤ b*d := by
        apply mul_le_mul
        any_goals assumption
        exact le_trans ha hab
      have := hmul_le_mul hx2_nonneg hx3_nonneg h1 h2
      have := hmul_le_mul (by positivity) hx4_nonneg this h3
      rw [hx] at this
      have : x^2 ≠ x^2 := by
        apply ne_of_lt
        rify
        refine lt_of_lt_of_le hpx this
      contradiction
    -- but we must have  $P < x^2$  for our solution.
    -- Hence  $0<=x<=29$  and we can easily find  $x$  to be  $24$  and  $0$ .
    interval_cases x
    any_goals norm_num at hx
    -- x=0
    left; rfl
    -- x=24
    right; rfl
