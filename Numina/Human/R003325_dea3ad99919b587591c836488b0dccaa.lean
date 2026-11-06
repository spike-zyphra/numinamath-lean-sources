import Mathlib

open Real Set
open scoped Real

/- if tan a = tan b
  and none of a and b are equal to (2 * k + 1) * π / 2 for some k -/
lemma Real_tan_eq {a b : ℝ} (h : Real.tan a = Real.tan b)
  (ha : ∀ (k : ℤ), a ≠ (2 * k + 1) * Real.pi / 2)
  (hb : ∀ (k : ℤ), b ≠ (2 * k + 1) * Real.pi / 2)
  : ∃ k : ℤ, a = b + k * Real.pi := by

    -- we'll use that tan is periodic

    -- π is positive
    have half_pos : 0 < π := by positivity

    -- let a = a' + ka * π
    -- and b = b' + kb * π, where a', b' ∈ [-π / 2, -(π / 2) + π)
    let a' := toIcoMod half_pos (-(π / 2)) a
    let b' := toIcoMod half_pos (-(π / 2)) b
    let ka := toIcoDiv half_pos (-(π / 2)) a
    let kb := toIcoDiv half_pos (-(π / 2)) b

    have a_eq : a' + ka • π = a := toIcoMod_add_toIcoDiv_zsmul half_pos (-(π / 2)) a
    have b_eq : b' + kb • π = b := toIcoMod_add_toIcoDiv_zsmul half_pos (-(π / 2)) b
    simp only [zsmul_eq_mul] at a_eq b_eq

    have mem_a : a' ∈ Set.Ico (-(π / 2)) (-(π / 2) + π) := toIcoMod_mem_Ico half_pos (-(π / 2)) a

    have mem_b : b' ∈ Set.Ico (-(π / 2)) (-(π / 2) + π) := toIcoMod_mem_Ico half_pos (-(π / 2)) b


    -- then we have that tan a' = tan b'
    simp only [←a_eq, ←b_eq, Real.tan_add_int_mul_pi] at h

    -- none of a' and b' are -π / 2
    have a'_ne : a' ≠ -(π / 2) := by
      by_contra eqq
      replace ha := eqq ▸ a_eq ▸ ha (ka - 1)
      push_cast at ha
      ring_nf at ha
      tauto

    have b'_ne : b' ≠ (-(π / 2)) := by
      by_contra eqq
      replace ha := eqq ▸ b_eq ▸ hb (kb - 1)
      push_cast at ha
      ring_nf at ha
      tauto

    -- so a', b' ∈ (-π / 2, -(π / 2) + π)
    replace mem_a : a' ∈ Set.Ioo (-(π / 2)) (-(π / 2) + π) := by
      convert_to a' ∈ (Set.Ico (-(π / 2)) (-(π / 2) + π)) \ {-(π / 2)}
      · exact Eq.symm Set.Ico_diff_left
      tauto

    replace mem_b : b' ∈ Set.Ioo (-(π / 2)) (-(π / 2) + π) := by
      convert_to b' ∈ (Set.Ico (-(π / 2)) (-(π / 2) + π)) \ {-(π / 2)}
      · exact Eq.symm Set.Ico_diff_left
      tauto

    -- using the injectivity of tan, we have a' = b'
    have a'_eq_b' : a' = b' := by
      simp only [Set.mem_Ioo, lt_neg_add_iff_add_lt] at mem_a
      simp only [Set.mem_Ioo, lt_neg_add_iff_add_lt] at mem_b
      apply Real.tan_inj_of_lt_of_lt_pi_div_two
      · tauto
      · linarith
      · tauto
      · linarith
      · exact h

    -- then we just need to show that b' + ka * π = b' + kb * π + k * π, for some k
    rw [←a_eq, ←b_eq, a'_eq_b']
    -- k = ka - kb works
    exists ka - kb
    push_cast
    ring

/- tan x is equal to 1 iff x is equal to π / 4 + k * π, for some integer k. -/
lemma tan_eq_one_iff (x : ℝ)
: tan x = 1 ↔ ∃ k : ℤ, x = Real.pi / 4 + k * Real.pi
  := by
    constructor
    · intro hx
      -- x is not one of the "undefined" values
      have x_ne : ∀ (k : ℤ), x ≠ (2 * ↑k + 1) * π / 2 := by
        intro k
        -- assume x is such a value
        by_contra x_eq
        replace x_eq : x = π / 2 + k * π := by linarith

        -- then tan x would be zero, but that's a contradiction
        norm_num [x_eq, Real.tan_add_int_mul_pi] at hx

      -- note that tan (π / 4) = 1
      -- so tan x = tan (π / 4)
      rw [←Real.tan_pi_div_four] at hx

      -- so we have our result
      apply Real_tan_eq hx x_ne
      -- then we just need to prove that π / 4 isn't an invalid value
      · intro k
        -- assume it is
        by_contra hh
        -- then π / 4 = π / 2 + k * π
        replace x_eq : π / 4 = π / 2 + k * π := by linarith

        -- but tan (π / 4) is equal to 1
        have eq_one : tan (π / 4) = 1 := by norm_num

        -- but if it's invalid it's equal to 0
        have ne_one : tan (π / 4) = 0 := by
          norm_num [x_eq, Real.tan_add_int_mul_pi]

        -- which is a contradiction
        linarith

    -- Every value of k works
    · rintro ⟨k, rfl⟩
      norm_num [Real.tan_add_int_mul_pi]

/- 8.317. $\frac{\sin ^{2} t-\tan^{2} t}{\cos ^{2} t-\cot^{2} t}+2 \tan^{3} t+1=0$. -/
theorem algebra_169444 (t : ℝ) (h1 : cos t ≠ 0) (h2 : sin t ≠ 0) :
  (sin t ^ 2 - tan t ^ 2) / (cos t ^ 2 - cot t ^ 2) + 2 * tan t ^ 3 + 1 = 0 ↔
  ∃ k : ℤ, t = (4 * k - 1) * π / 4 := by

    -- the leftmost term can be simplified to (tan t ^ 3) ^ 2
    have left_term_eq : (sin t ^ 2 - tan t ^ 2) / (cos t ^ 2 - t.cot ^ 2)
      = (tan t ^ 3) ^ 2 := by
        -- we chain equalities
        calc
          -- rewrite tan t as sin t / cos t and cot t as cos t / sin t
          _ = (sin t ^ 2 - (sin t ^ 2) / (cos t ^ 2)) / (cos t ^ 2 - (cos t ^ 2) / (sin t ^ 2)) := by
            congr
            · rw [Real.tan_eq_sin_div_cos]
              ring
            · rw [Real.cot_eq_cos_div_sin]
              ring
          -- multiply terms with denominator of fraction which is subtracted
          _ = ((sin t ^ 2 * cos t ^ 2) / cos t ^ 2 - sin t ^ 2 / cos t ^ 2) / ((cos t ^ 2 * sin t ^ 2) / sin t ^ 2 - cos t ^ 2 / sin t ^ 2) := by
            congr
            · field_simp
            · field_simp
          -- , combine to common fractions
          _ = ((sin t ^ 2 * cos t ^ 2 - sin t ^ 2) / cos t ^ 2) / ((cos t ^ 2 * sin t ^ 2 - cos t ^ 2) / sin t ^ 2) := by
            rw [div_sub_div_same, div_sub_div_same]
          -- group terms in numerators
          _ = (sin t ^ 2 * (cos t ^ 2 - 1)) / cos t ^ 2 / ((cos t ^ 2 * (sin t ^ 2 - 1)) / sin t ^ 2) := by ring
          -- simplify using sin t ^ 2 + cos t ^ 2 = 1
          _ = (sin t ^ 2 * (-sin t ^ 2)) / cos t ^ 2 / ((cos t ^ 2 * (-cos t ^ 2)) / sin t ^ 2) := by
            congr
            · rw [Real.sin_sq]
              ring
            · rw [Real.sin_sq]
              ring
          -- combine everythign into one fraction
          _ = (sin t ^ 2 * sin t ^ 2 * sin t ^ 2 ) / (cos t ^ 2 * cos t ^ 2 * cos t ^ 2) := by
            field_simp
            linarith
          -- but the numerator us just sin, and the denominator just cos, so it's equal to (tan t ^ 3) ^ 2
          _ = (tan t ^ 3) ^ 2 := by
            rw [Real.tan_eq_sin_div_cos]
            ring

    rw [left_term_eq]

    -- then the LHS is equal to (tan t ^ 3 + 1) ^ 2
    trans (tan t ^ 3 + 1) ^ 2 = 0
    · refine Eq.congr ?_ rfl
      ring

    -- which is zero iff tan t ^ 3 + 1 is zero
    trans tan t ^ 3 + 1 = 0
    · norm_num

    -- we move -1 to RHS and notice that taking -1 to the power of 3 doesn't change the result
    trans tan t ^ 3 = (-1) ^ 3
    · constructor <;> (intro; linarith)

    -- but that holds iff tan t is -1
    trans tan t = -1
    -- because three is odd
    · have three_odd : Odd 3 := by decide
      exact (three_odd.strictMono_pow (R := ℝ)).injective.eq_iff

    -- which means that tan -t is 1
    trans tan (-t) = 1
    · norm_num
      constructor <;> (intro; linarith)

    -- and if tan -t is 1, we know the possible values of -t
    rw [tan_eq_one_iff]

    -- which is pretty much as wanted
    constructor
    all_goals
    · intro ⟨k, hh⟩
      exists -k
      push_cast
      linarith