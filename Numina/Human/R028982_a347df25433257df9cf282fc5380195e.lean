import Mathlib
open Real
/- Example 4: Let $0 \leq a, b, c \leq \lambda(\lambda>0)$, prove:
$$\frac{a}{\lambda^{2}+b c}+\frac{b}{\lambda^{2}+c a}+\frac{c}{\lambda^{2}+a b} \leq \frac{2}{\lambda} .$$ -/
theorem inequalities_600706 (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ t) (hb1 : b ≤ t) (hc1 : c ≤ t) (ht : t > 0) : a / (t ^ 2 + b * c) + b / (t ^ 2 + c * a) + c / (t ^ 2 + a * b) ≤ 2 / t:= by
  -- First, we prove an upper bound for the first fraction
  have g1 : a / (t ^ 2 + b * c) ≤ a / (a + b + c) * (2 / t):= by
    field_simp
    -- Handle the case where a = 0 separately
    by_cases ha2 : a = 0
    .
      subst a
      simp
    .
      -- For a > 0, we proceed with algebraic manipulations
      replace ha : a > 0:= by exact lt_of_le_of_ne ha fun a_1 => ha2 (id (Eq.symm a_1))
      clear ha2
      rw [show a / (t ^ 2 + b * c) = a * (1 / (t ^ 2 + b * c)) by field_simp]
      rw [show a * 2 / ((a + b + c) * t) = a * (2 / ((a + b + c) * t)) by ring]
      -- Reduce to proving an inequality without the factor a
      suffices 1 / (t ^ 2 + b * c) ≤ 2 / ((a + b + c) * t) by exact (mul_le_mul_iff_of_pos_left ha).mpr this
      -- Multiply both sides by positive values to simplify comparison
      have g1 : (t ^ 2 + b * c) * ((a + b + c) * t) > 0:= by positivity
      suffices (t ^ 2 + b * c) * ((a + b + c) * t) * (1 / (t ^ 2 + b * c)) ≤ (t ^ 2 + b * c) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) by exact le_of_mul_le_mul_left this g1
      -- Simplify both sides of the inequality
      rw [show (t ^ 2 + b * c) * ((a + b + c) * t) * (1 / (t ^ 2 + b * c)) = (a + b + c) * t by field_simp]
      rw [show (t ^ 2 + b * c) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) = 2 * (t ^ 2 + b * c) by field_simp ; linarith]
      -- Rearrange to a form that can be proven non-negative
      suffices (t - b) * (t - c) + b * c + t * (t - a) ≥ 0 by linarith
      -- Use the bounds on a, b, c to show all terms are non-negative
      replace ha1 : t - a ≥ 0:= by linarith
      replace hb1 : t - b ≥ 0:= by linarith
      replace hc1 : t - c ≥ 0:= by linarith
      positivity

  -- Similarly, prove an upper bound for the second fraction
  have g2 : b / (t ^ 2 + c * a) ≤ b / (a + b + c) * (2 / t):= by
    field_simp
    -- Handle the case where b = 0 separately
    by_cases hb2 : b = 0
    .
      subst b
      simp
    .
      -- For b > 0, follow similar steps as for the first fraction
      replace hb : b > 0:= by exact lt_of_le_of_ne hb fun b_1 => hb2 (id (Eq.symm b_1))
      clear hb2
      rw [show b / (t ^ 2 + c * a) = b * (1 / (t ^ 2 + c * a)) by field_simp]
      rw [show b * 2 / ((a + b + c) * t) = b * (2 / ((a + b + c) * t)) by ring]
      suffices 1 / (t ^ 2 + c * a) ≤ 2 / ((a + b + c) * t) by exact (mul_le_mul_iff_of_pos_left hb).mpr this
      have g1 : (t ^ 2 + c * a) * ((a + b + c) * t) > 0:= by positivity
      suffices (t ^ 2 + c * a) * ((a + b + c) * t) * (1 / (t ^ 2 + c * a)) ≤ (t ^ 2 + c * a) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) by exact le_of_mul_le_mul_left this g1
      rw [show (t ^ 2 + c * a) * ((a + b + c) * t) * (1 / (t ^ 2 + c * a)) = (a + b + c) * t by field_simp]
      rw [show (t ^ 2 + c * a) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) = 2 * (t ^ 2 + c * a) by field_simp ; linarith]
      suffices (t - c) * (t - a) + c * a + t * (t - b) ≥ 0 by linarith
      replace ha1 : t - a ≥ 0:= by linarith
      replace hc1 : t - c ≥ 0:= by linarith
      replace hb1 : t - b ≥ 0:= by linarith
      positivity

  -- Prove an upper bound for the third fraction
  have g3 : c / (t ^ 2 + a * b) ≤ c / (a + b + c) * (2 / t):= by
    field_simp
    -- Handle the case where c = 0 separately
    by_cases hc2 : c = 0
    .
      subst c
      simp
    .
      -- For c > 0, follow similar steps as for the previous fractions
      replace hc : c > 0:= by exact lt_of_le_of_ne hc fun c_1 => hc2 (id (Eq.symm c_1))
      clear hc2
      rw [show c / (t ^ 2 + a * b) = c * (1 / (t ^ 2 + a * b)) by field_simp]
      rw [show c * 2 / ((a + b + c) * t) = c * (2 / ((a + b + c) * t)) by ring]
      suffices 1 / (t ^ 2 + a * b) ≤ 2 / ((a + b + c) * t) by exact (mul_le_mul_iff_of_pos_left hc).mpr this
      have g1 : (t ^ 2 + a * b) * ((a + b + c) * t) > 0:= by positivity
      suffices (t ^ 2 + a * b) * ((a + b + c) * t) * (1 / (t ^ 2 + a * b)) ≤ (t ^ 2 + a * b) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) by exact le_of_mul_le_mul_left this g1
      rw [show (t ^ 2 + a * b) * ((a + b + c) * t) * (1 / (t ^ 2 + a * b)) = (a + b + c) * t by field_simp]
      rw [show (t ^ 2 + a * b) * ((a + b + c) * t) * (2 / ((a + b + c) * t)) = 2 * (t ^ 2 + a * b) by field_simp ; linarith]
      suffices (t - a) * (t - b) + a * b + t * (t - c) ≥ 0 by linarith
      replace ha1 : t - a ≥ 0:= by linarith
      replace hb1 : t - b ≥ 0:= by linarith
      replace hc1 : t - c ≥ 0:= by linarith
      positivity

  -- Handle the special case where a = 0
  by_cases ha2 : a = 0
  .
    subst a
    simp
    field_simp
    have g4 : t ^ 2 > 0:= by positivity
    suffices b + c ≤ 2 / t * t ^ 2 by exact (div_le_iff₀ g4).mpr this
    rw [show 2 / t * t ^ 2 = 2 * t by field_simp ; linarith]
    linarith
  .
    -- For a > 0, combine the three upper bounds to complete the proof
    replace ha : a > 0:= by exact lt_of_le_of_ne ha fun a_1 => ha2 (id (Eq.symm a_1))
    clear ha2
    -- Show that the sum of the upper bounds equals 2/t
    have g4 : a / (a + b + c) * (2 / t) + b / (a + b + c) * (2 / t) + c / (a + b + c) * (2 / t) = 2 / t:= by
      field_simp
      linarith
    -- Combine all inequalities to complete the proof
    linarith
