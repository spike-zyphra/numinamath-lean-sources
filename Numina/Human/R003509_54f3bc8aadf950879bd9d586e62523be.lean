import Mathlib

/- cos (4 * s) is equal to 1 - 2 * Real.sin (2 * x) ^ 2. -/
lemma Real_cos_four_mul (x : ℝ) : Real.cos (4 * x)
  = 1 - 2 * Real.sin (2 * x) ^ 2 := by
    -- use double angle formula, and square of cos formula
    convert_to Real.cos (2 * (2 * x)) = _
    · ring_nf
    rw [Real.cos_two_mul', Real.cos_sq']

    -- simplify
    ring

/- If sin (2 * x) = 1 / 2 then there's some integer k such that
  x = π / 12 + π * k
  or x = 5 * π / 12 + π * k. -/
lemma Real_sin_two_mul_eq_one_div_two {x : ℝ} (h : Real.sin (2 * x) = 1 / 2)
  : ∃ k : ℤ, (x = Real.pi / 12 + Real.pi * k ∨ x = 5 * Real.pi / 12 + Real.pi * k):= by
    rw [←Real.sin_pi_div_six, Real.sin_eq_sin_iff] at h
    rcases h with ⟨k, (h1 | h2)⟩
    · exists -k
      refine Or.inl ?_
      push_cast
      linarith
    · exists k
      refine Or.inr ?_
      linarith

/- Integers mod three has three cases. -/
lemma Int_three_cases (k : ℤ)
  : ∃ m, (k = 3 * m ∨ k = 3 * m + 1 ∨ k = 3 * m + 2) := by
    have k_eq : k = 3 * (k / 3) + k % 3 := (Int.ediv_add_emod k 3).symm
    exists k / 3
    have : k % 3 < 3 := Int.emod_lt_of_pos k (by omega)
    have : 0 ≤ k % 3 := Int.emod_nonneg k (by omega)
    interval_cases k % 3
    · refine Or.inl ?_
      nth_rw 1 [k_eq]
      norm_num
    · refine Or.inr <| Or.inl ?_
      nth_rw 1 [k_eq]
    · refine Or.inr <| Or.inr ?_
      nth_rw 1 [k_eq]


/- 8.124. $\operatorname{tg} x+\operatorname{ctg} x=2 \cos^{-1} 4 x$. -/
theorem algebra_189394 (x : ℝ)
  (hs : Real.sin x ≠ 0)
  (hc : Real.cos x ≠ 0)
  (hc4 : Real.cos (4 * x) ≠ 0) :
  Real.tan x + Real.cot x = 2 / Real.cos (4 * x) ↔
  ∃ k : ℤ, x = (Real.pi / 12) * (4 * k + 1) := by
    -- Using trig formulas we have that 1 - 2 * Real.sin (2 * x) ^ 2 is non-zero
    have ne_zero_1 : 1 - 2 * Real.sin (2 * x) ^ 2 ≠ 0 := by
      norm_num [←Real_cos_four_mul]
      tauto
    -- and that Real.sin (2 * x) is non-zero
    have ne_zero_2 : Real.sin (2 * x) ≠ 0 := by
      norm_num [Real.sin_two_mul]
      tauto

    -- simplify the LHS expression to just use sin and cos
    have lhs_eq : Real.tan x + Real.cot x - 2 / Real.cos (4 * x)
      = 2 * (Real.sin (2 * x))⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2)⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2 - Real.sin (2 * x)) := by
        calc
          -- rewrite to only contain sin and cos
          _ = Real.sin x / Real.cos x + Real.cos x / Real.sin x - 2 / Real.cos (4 * x) := by
            rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
          -- combine fractions
          _ = ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) / (Real.cos x * Real.sin x) - 2 / Real.cos (4* x) := by
            ring_nf
            field_simp
            ring
          -- simplify left term using trig identities
          _ = 2 / Real.sin (2 * x) - 2 / Real.cos (4 * x) := by
            rw [Real.sin_sq_add_cos_sq, Real.sin_two_mul]
            ring
          -- simplify left term using trig identities
          _ = 2 * (1 / Real.sin (2 * x) - 1 / Real.cos (4 * x)) := by ring
          -- simplify right term using trig identities
          _ = 2 * (1 / Real.sin (2 * x) - 1 / (1 - 2 * Real.sin (2 * x) ^ 2)) := by rw [Real_cos_four_mul]
          -- avoid divisions, factorize
          _ = 2 * (Real.sin (2 * x))⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2)⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2 - Real.sin (2 * x)) := by
            field_simp

    -- LHS is zero iff 2 * sin (2 * x) ^ 2 + sin (2 * x) - 1 = 0
    have lhs_iff : Real.tan x + x.cot = 2 / Real.cos (4 * x)
      ↔ 2 * Real.sin (2 * x) ^ 2 + Real.sin (2 * x) - 1 = 0 := by
        calc
          -- move all terms to LHS
          _ ↔ Real.tan x + x.cot - 2 / Real.cos (4 * x) = 0 := by
            constructor <;> (intro; linarith)
          -- use our simplification which containing just sin and cos
          _ ↔ 2 * (Real.sin (2 * x))⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2)⁻¹ * (1 - 2 * Real.sin (2 * x) ^ 2 - Real.sin (2 * x)) = 0 := by
            rw [lhs_eq]
          -- disregard non-zero factors
          _ ↔ 1 - 2 * Real.sin (2 * x) ^ 2 - Real.sin (2 * x) = 0 := by norm_num [ne_zero_1, ne_zero_2]
          -- multiply both sides by -1
          _ ↔ -(1 - 2 * Real.sin (2 * x) ^ 2 - Real.sin (2 * x)) = 0 := Iff.symm neg_eq_zero
          -- simplify
          _ ↔ 2 * Real.sin (2 * x) ^ 2 + Real.sin (2 * x) - 1 = 0 := by ring_nf

    rw [lhs_iff]

    -- note that 2 * x ^ 2 + x - 1 can be factored as 2 * (x + 1) * (x - (1 / 2))
    have split : ∀ x : ℝ, 2 * x ^ 2 + x - 1 = 2 * (x + 1) * (x - (1 / 2)) := by
      intro x
      ring

    -- apply it to our case where we have 2 * (sin (2x)) ^ 2 + (sin (2x)) - 1
    rw [split]

    -- simplify
    norm_num

    -- so then we have that sin (2x) is -1 or 1 / 2
    trans Real.sin (2 * x) = -1 ∨ Real.sin (2 * x) = 1 / 2
    · exact or_congr eq_neg_iff_add_eq_zero.symm sub_eq_zero

    -- then we can show that both sides imply each other
    constructor
    -- consider values of sin (2x)
    · rintro (neg_one | half)
      -- when sin (2x) = -1
      -- then -(π / 2) + k * (2 * π) = 2 * x
      · obtain ⟨k, kh⟩ := Real.sin_eq_neg_one_iff.mp neg_one
        -- meaning x = π / 12 * (4 * (3 * k - 1) + 1)
        exists 3 * k - 1
        norm_num
        linarith
      -- when sin (2x) = 1 / 2
      · rcases Real_sin_two_mul_eq_one_div_two half with ⟨k, (h1 | h2)⟩
        -- then either π / 12 + π * k
        -- meaning x = π / 12 * (4 * (3 * k) + 1)
        · exists 3 * k
          norm_num
          linarith
        -- or 5π / 12 + π * k
        -- meaning x = π / 12 * (4 * (3 * k + 1) + 1)
        · exists 3 * k + 1
          norm_num
          linarith
    -- consider when x = π / 12 * (4 * k + 1)
    · intro ⟨k, kh⟩
      rw [kh]
      ring_nf
      -- then k % 3 has three possible values
      rcases Int_three_cases k with ⟨k, (rfl | rfl | rfl)⟩
      -- consider k = 3 * k_0
      · norm_num
        ring_nf
        -- then it's equal to 1 / 2
        refine Or.inr ?_
        convert_to Real.sin (Real.pi / 6 + k * (2 * Real.pi)) = 1 / 2
        · ring_nf
        norm_num
      -- consider k = 3 * k_0 + 1
      · norm_num
        ring_nf
        -- then it's equal to 1 / 2
        refine Or.inr ?_
        convert_to Real.sin ((Real.pi - Real.pi / 6) + k * (2 * Real.pi)) = 1 / 2
        · ring_nf
        norm_num
      -- consider k = 3 * k_0 + 2
      · norm_num
        ring_nf
        -- then it's equal to -1
        refine Or.inl ?_
        convert_to Real.sin ((Real.pi / 2 + Real.pi) + k * (2 * Real.pi)) = -1
        · ring_nf
        norm_num