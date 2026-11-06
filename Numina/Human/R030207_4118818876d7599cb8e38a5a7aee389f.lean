import Mathlib

open Real Set
open scoped Real

/- Solve the following equation:

$$
\frac{1}{\sin x}-\frac{1}{\sin 2 x}=\frac{2}{\sin 4 x}
$$ -/
theorem algebra_215439 (x : ℝ)
  (h_sin_x : sin x ≠ 0) (h_sin_2x : sin (2 * x) ≠ 0) (h_sin_4x : sin (4 * x) ≠ 0) :
  1 / sin x - 1 / sin (2 * x) = 2 / sin (4 * x) ↔
  ∃ n : ℤ, x = 2 * π / 3 + 2 * n * π ∨ x = -2 * π / 3 + 2 * n * π := by

  -- Transform the denominators using the known angle sum formulas
  have eq_sin_2x : sin (2 * x) = 2 * sin x * cos x := by exact sin_two_mul x
  have eq_sin_4x : sin (4 * x) = 4 * sin x * cos x * (2 * cos x ^ 2 - 1) := by
    rw [
      show 4 * x = 2 * (2 * x) by ring,
      sin_two_mul,
      sin_two_mul,
      cos_two_mul
    ]
    ring

  rw [eq_sin_2x] at h_sin_2x ⊢
  rw [eq_sin_4x] at h_sin_4x ⊢

  -- we derive that cos x ≠ 0 as it appears as a factor in the denominators
  have h_cos_x : cos x ≠ 0 := by
    by_contra! h
    rw [h] at h_sin_2x
    simp at h_sin_2x

  -- bring to the common denominator
  have : 1 / sin x - 1 / (2 * sin x * cos x) =
    (4 * cos x * (2 * cos x ^ 2 - 1) - 2 * (2 * cos x ^ 2 - 1)) / (4 * sin x * cos x * (2 * cos x ^ 2 - 1)) := by field_simp; ring
  rw [this]

  -- then we deduce the numerators are equal, thus
  --  4 * cos x * (2 * cos x ^ 2 - 1) - 2 * (2 * cos x ^ 2 - 1) - 2 = 0
  rw [div_left_inj' h_sin_4x, ← sub_eq_zero]
  -- simplify the formula, we get cos x * (2 * cos x ^ 2 - cos x - 1) = 0
  rw [show
    4 * cos x * (2 * cos x ^ 2 - 1) - 2 * (2 * cos x ^ 2 - 1) - 2 =
    4 * cos x * (2 * cos x ^ 2 - cos x - 1) by ring]
  simp [h_cos_x]

  -- factor 2 * cos x ^ 2 - cos x - 1 into 2 * (cos x - 1) * (cos x + 1 / 2)
  have : 2 * cos x ^ 2 - cos x - 1 = 2 * (cos x - 1) * (cos x + 1 / 2) := by ring
  rw [this]

  -- as sin x ≠ 0, we show that cos x ≠ 1
  have : cos x ≠ 1 := by
    by_contra! h
    have : cos x ^ 2 = 1 := by rw [h]; ring
    have : sin x ^ 2 = 0 := by rw [sin_sq, this]; ring
    have : sin x = 0 := sq_eq_zero_iff.mp this
    contradiction

  have : cos x - 1 ≠ 0 := by
    by_contra! h
    rw [sub_eq_zero] at h
    contradiction

  -- thus the only root if 2 * (cos x - 1) * (cos x + 1 / 2) is cos x = -1 / 2
  simp [this]

  constructor
  · -- we prove the only-if part
    intro h_cos_x -- so we assume cos x = -1 / 2
    have : -cos x = 1 / 2 := by simp; linarith
    rw [← cos_pi_sub] at this -- and we deduce cos (π - x) = 1 / 2

    -- we need to transform RHS to 1 in order to use lemmas in mathlib
    -- so we have cos ((π - x) - (π / 3)) = 1 or cos ((π - x) + (π / 3)) = 1
    have : cos ((π - x) - (π / 3)) = 1 ∨ cos ((π - x) + (π / 3)) = 1  := by
      rw [cos_sub, cos_add]
      rw [cos_pi_div_three, sin_pi_div_three, sin_pi_sub, this]
      have : |sin x| = √ 3 / 2 := by
        rw [Real.abs_sin_eq_sqrt_one_sub_cos_sq]
        rw [show cos x = -2⁻¹ by linarith]
        norm_num
        congr
        refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
        norm_num
        norm_num
      rw [abs_eq] at this
      rcases this with h | h
      · rw [h]
        left
        field_simp
        norm_num
      · rw [h]
        right
        field_simp
        norm_num
      apply div_nonneg
      exact sqrt_nonneg 3
      norm_num

    -- now we handle the two cases
    rcases this with h_cos | h_cos
    · -- 1. cos ((π - x) - (π / 3)) = 1, then we have x = 2π/3 + 2nπ
      rw [cos_eq_one_iff] at h_cos
      obtain ⟨n, hn⟩ := h_cos
      rw [show π - x - π / 3 = 2 * π / 3 - x by ring] at hn
      use -n
      left
      rw [Int.cast_neg]
      linarith
    · -- 2. cos ((π - x) + (π / 3)) = 1, then we have x = -2π/3 + 2nπ
      rw [cos_eq_one_iff] at h_cos
      obtain ⟨n, hn⟩ := h_cos
      rw [show π - x + π / 3 = 2 * π - (2 * π / 3 + x) by ring] at hn
      have : x = (1 - n) * 2 * π - 2 * π / 3 := by linarith
      use 1 - n
      right
      rw [Int.cast_sub]
      simp
      linarith
  · -- we prove the if part
    rintro ⟨n, hn⟩  -- so x = ± 2π / 3 + 2nπ
    -- break into positive and negarive cases, replace x with its value
    -- then the evaluation of trangle functions are trivial
    rcases hn with hn | hn
    · rw [hn, show (2 * n * π : ℝ) = n * (2 * π) by ring]
      simp
      rw [show 2 * π / 3 = π - π / 3 by ring]
      simp
    · rw [hn,
        show (2 * n * π : ℝ) = n * (2 * π) by ring,
        show (-(2 * π) / 3) = -((2 * π) / 3) by ring]
      simp
      rw [show 2 * π / 3 = π - π / 3 by ring]
      simp
