import Mathlib

open Real Set
open scoped BigOperators

/- Given $a>0, b>0$, if $x$ represents the smallest of the three numbers $1$, $a$, and $\frac{b}{{{a}^{2}}+{{b}^{2}}}$, then the maximum value of $x$ as $a, b$ vary is ___          ___. -/
theorem inequalities_12445 :
  IsGreatest {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = min (min 1 a) (min a (b / (a ^ 2 + b ^ 2)))} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt(2)/2 is in the set
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show a > 0
      have hsqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num)]
    constructor
    · -- Show b > 0
      have hsqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num)]
    · -- Show x = ...
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        nlinarith [h1]
      have h3sqrt2_pos : Real.sqrt 2 > 0 := by positivity
      norm_num [h1, h2, Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)]
      <;> ring_nf
      <;> norm_num [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)]
      all_goals
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num), Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)]
  · -- Show that sqrt(2)/2 is the greatest value in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    by_contra h
    push_neg at h
    have h1 : x > Real.sqrt 2 / 2 := h
    rw [hx] at h1
    by_cases h4 : (min (min 1 a) (min a (b / (a ^ 2 + b ^ 2))) ) ≤ Real.sqrt 2 / 2
    · linarith
    · -- Assume that (min (min 1 a) (min a (b / (a ^ 2 + b ^ 2))) ) > Real.sqrt 2 / 2
      have h0 : min (min 1 a) (min a (b / (a ^ 2 + b ^ 2))) > Real.sqrt 2 / 2 := h1
      -- Sub-cases:
      -- From h0, we know that all three terms in the minimum are > sqrt(2)/2
      have h5sqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)
      have ha0 : a > Real.sqrt 2 / 2 := by
        by_contra h
        push_neg at h
        have h7a : min (min 1 a) (min a (b / (a ^ 2 + b ^ 2))) ≤ a := by
          simp [min_le_iff]
          all_goals
            nlinarith
        have h9a : a ≤ Real.sqrt 2 / 2 := by
          nlinarith
        nlinarith
      -- Show the b side needs to be bad
      have hb0 : b / (a ^ 2 + b ^ 2) > Real.sqrt 2 / 2 := by
        by_contra h
        push_neg at h
        have h8 : min (min 1 a) (min a (b / (a ^ 2 + b ^ 2))) ≤ b / (a ^ 2 + b ^ 2) := by
          simp [min_le_iff]
          all_goals
            nlinarith
        have h10 : b / (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 / 2 := by
          nlinarith
        nlinarith
      have hb1 : b > Real.sqrt 2 / 2 := by
        by_contra h
        push_neg at h
        have h8 : b ≤ Real.sqrt 2 / 2 := by
          nlinarith
        have h9 : b / (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 / 2 := by
          have h10 : a ^ 2 ≥ (Real.sqrt 2 / 2) ^ 2 := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h11 : b ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := by
            nlinarith [Real.sqrt_nonneg 2, h8]
          have h12 : a ^ 2 + b ^ 2 ≥ (Real.sqrt 2 / 2) ^ 2 := by
            nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          apply (div_le_iff₀ (by nlinarith)).mpr
          nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a + b), sq_nonneg (a - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a^ 2 + b ^2), sq_nonneg (a * b)]
      have h7 : (a ^ 2 + b ^ 2) > 0 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
      -- Now we start the derivations
      -- We know sqrt 2 /2 < b / (a^2 + b ^ 2)
      have h10 : b > (Real.sqrt 2 / 2) * (a ^ 2 + b ^ 2) := by
        have h11 : (b / (a ^ 2 + b ^ 2)) > Real.sqrt 2 / 2 := hb0
        have : b / (a ^ 2 + b ^ 2) > Real.sqrt 2 / 2 := h11
        have h10 : b > (Real.sqrt 2 / 2) * (a ^ 2 + b ^ 2) := by
          have h11 : (a ^ 2 + b ^ 2) > 0 := h7
          apply (lt_div_iff₀ (by nlinarith)).mp at this
          nlinarith
        nlinarith
      -- We now derive the contradiction
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (a * b), sq_nonneg ( (Real.sqrt 2 ^ 2) ), sq_nonneg (a - b), sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (b ^ 2 - 1 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - Real.sqrt 2 / 2), sq_nonneg (b - Real.sqrt 2 / 2)]