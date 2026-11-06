import Mathlib

/- Given positive real numbers a and b, then (a / b) ^ (a - b) is at least 1. -/
lemma div_pow_sub_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  : 1 ≤ (a / b) ^ (a - b) := by
    -- consider order cases of a and b
    rcases lt_trichotomy a b with lee | eqq | gtt
    -- when a < b, it's a strict inequality
    · refine le_of_lt ?_
      apply Real.one_lt_rpow_of_pos_of_lt_one_of_neg
      -- a / b is positive
      · positivity
      -- a / b is less than 1
      · exact Bound.div_lt_one_of_pos_of_lt hb lee
      -- a - b is negative
      · exact sub_neg.mpr lee
    -- when a = b, then (a / a) ^ (a - a) = 1 ^ 0 = 1
    · norm_num [eqq]
    -- when b < a, it's a strict inequality
    · refine le_of_lt ?_
      apply Real.one_lt_rpow
      -- a / b is at least one
      · exact (one_lt_div hb).mpr gtt
      -- a - b is positive
      · linarith

/- Prove that if $a, b$, and $c$ are any positive integers, then the cube of the number $a^{a} b^{b} c^{c}$ cannot be less than the $(a+b+c)$-th power of the product $a b c$. -/
theorem inequalities_181033 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^a * b^b * c^c)^3 ≥ (a * b * c)^(a + b + c) := by
    -- use ≤ instead of ≥
    simp only [ge_iff_le]

    -- consider it as real numbers
    rify

    -- the LHS is positive
    have left_pos : 0 < ((a * b * c) ^ (a + b + c) : ℝ) := by positivity

    -- so divide both sides by the LHS
    rw [←one_le_div₀ left_pos]

    -- a b c are all positive
    have a_pos : 0 < (a : ℝ) := by norm_cast
    have b_pos : 0 < (b : ℝ) := by norm_cast
    have c_pos : 0 < (c : ℝ) := by norm_cast

    -- simplify the RHS, group into three terms
    have eq : (a ^ a * b ^ b * c ^ c : ℝ) ^ 3 / (a * b * c) ^ (a + b + c)
      = (a / b) ^ (a - b : ℝ) * (a / c) ^ (a - c : ℝ) * (b / c) ^ (b - c : ℝ) := by
      calc
        -- distribute powers
        _ = (a ^ (3 * a) * b ^ (3 * b) * c ^ (3 * c) : ℝ) / (a  ^ (a + b + c) * b  ^ (a + b + c) * c ^ (a + b + c)) := by ring
        -- consider powers as real numbers
        _ = (a ^ (3 * a : ℝ) * b ^ (3 * b : ℝ) * c ^ (3 * c : ℝ) : ℝ) / (a  ^ (a + b + c : ℝ) * b  ^ (a + b + c : ℝ) * c ^ (a + b + c : ℝ)) := by norm_cast
        -- group powers into a b and c powers
        _ = ((a ^ (3 * a : ℝ) / a  ^ (a + b + c : ℝ)) * (b ^ (3 * b : ℝ) / b  ^ (a + b + c : ℝ)) * (c ^ (3 * c : ℝ) : ℝ) / c ^ (a + b + c : ℝ)) := by ring
        -- remove fractions
        _ = ((a ^ (3 * a - (a + b + c) : ℝ)) * b ^ (3 * b - (a + b + c) : ℝ) * (c ^ (3 * c - (a + b + c): ℝ) : ℝ)) := by
          rw [Real.rpow_sub a_pos, Real.rpow_sub b_pos, Real.rpow_sub c_pos]
          ring
        -- group values in powers
        _ = (a ^ ((a - b) + (a - c) : ℝ)) * b ^ ((b - c) - (a - b) : ℝ) * (c ^ (-(a - c) - (b - c) : ℝ)) := by ring_nf
        -- bring back fractions
        _ = (a ^ (a - b : ℝ) * a ^ (a - c : ℝ)) * (b ^ (b - c : ℝ) / b ^ (a - b : ℝ)) * (c ^ (-(a - c) : ℝ) / c ^ (b - c : ℝ)) := by
          rw [Real.rpow_sub b_pos, Real.rpow_sub c_pos, ←Real.rpow_add a_pos]
        -- a negative fraction becomes a fraction too
        _ = (a ^ (a - b : ℝ) * a ^ (a - c : ℝ)) * b ^ (b - c : ℝ) / b ^ (a - b : ℝ) * 1 / c ^ (a - c : ℝ) * 1 / c ^ (b - c : ℝ) := by
          rw [Real.rpow_neg <| le_of_lt c_pos]
          ring
        -- then we group terms with common powers
        _ = (a ^ (a - b : ℝ) / b ^ (a - b : ℝ)) * b ^ (b - c : ℝ) / c ^ (b - c : ℝ) * a ^ (a - c : ℝ) / c ^ (a - c : ℝ) := by ring
        -- then we have three fractions to some power
        _ = (a / b) ^ (a - b : ℝ) * (b / c) ^ (b - c : ℝ) * (a / c) ^ (a - c : ℝ) := by
          rw [Real.div_rpow (le_of_lt a_pos) (le_of_lt b_pos)]
          rw [Real.div_rpow (le_of_lt b_pos) (le_of_lt c_pos)]
          rw [Real.div_rpow (le_of_lt a_pos) (le_of_lt c_pos)]
          ring
        -- rearrange terms
        _ = _ := by ring

    rw [eq]

    -- each term is at least 1
    have term_1 := div_pow_sub_pos a_pos b_pos
    have term_2 := div_pow_sub_pos a_pos c_pos
    have term_3 := div_pow_sub_pos b_pos c_pos

    -- so their product is at least 1
    convert_to (1 * 1 * 1 : ℝ) ≤ _
    · ring
    gcongr