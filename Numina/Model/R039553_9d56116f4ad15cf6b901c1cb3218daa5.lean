import Mathlib

theorem algebra_62985 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.sin x ^ 4 / 42 + Real.cos x ^ 4 / 75 = 1 / 117) :
    Real.tan x = Real.sqrt 14 / 5 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h6 : 75 * 117 * Real.sin x ^ 4 + 42 * 117 * Real.cos x ^ 4 = 42 * 75 := by
    have h7 : Real.sin x ^ 4 / 42 + Real.cos x ^ 4 / 75 = 1 / 117 := h
    field_simp at h7 ⊢
    nlinarith [h3, sq_nonneg (Real.sin x * Real.cos x), sq_nonneg (Real.sin x ^ 2 - 14 / 39), sq_nonneg (Real.cos x ^ 2 - 25 / 39)]
  -- Substitute cos^4 = (1 - sin^2)^2
  have h7 : (Real.sin x ^ 2) = 14 / 39 := by
    nlinarith [h3, h6, sq_nonneg (Real.sin x ^ 2 - 14 / 39), sq_nonneg (Real.cos x ^ 2 - 25 / 39), h1, sq_nonneg (Real.sin x ^ 2 - 14 / 39), sq_nonneg (Real.cos x ^ 2 - 25 / 39)]
  -- Substitute cos^4 = (1 - sin^2)^2
  have h8 : (Real.cos x) ^ 2 = 25 / 39 := by
    nlinarith [h3, h7]
  -- Use tan^2(x) = sin^2(x)/cos^2(x)
  have h9 : Real.tan x ^ 2 = 14 / 25 := by
    have h10 : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h10]
    have h11 : (Real.sin x / Real.cos x) ^ 2 = (Real.sin x ^ 2) / (Real.cos x ^ 2) := by
      field_simp
    rw [h11]
    rw [h7, h8]
    all_goals
      norm_num
  -- Let's compute the square root
  have h12 : Real.tan x > 0 := by
    have h13 : Real.sin x > 0 := h1
    have h14 : Real.cos x > 0 := h2
    have h15 : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h15]
    apply div_pos
    all_goals
      linarith
  have h13 : Real.tan x = Real.sqrt (14 / 25) := by
    have h14 : Real.tan x ^ 2 = 14 / 25 := h9
    have h122 : Real.tan x > 0 := h12
    have h16 : Real.tan x = Real.sqrt (14 / 25) := by
      have h117 : (Real.tan x) ^ 2 = (14 / 25 : ℝ) := h14
      have h118 : Real.tan x ≥ 0 := by linarith
      have h119 : Real.sqrt ((Real.tan x) ^ 2) = Real.tan x := by
        rw [Real.sqrt_sq]
        linarith
      have h120 : Real.sqrt ((14 / 25 : ℝ)) = Real.sqrt ((Real.tan x) ^ 2) := by
        rw [h117]
      have h121 : Real.sqrt ((14 / 25 : ℝ)) = Real.tan x := by
        rw [h120, h119]
      linarith
    linarith
  -- Simplify sqrt(14/25)
  have h14 : Real.sqrt (14 / 25 : ℝ) = Real.sqrt 14 / 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  -- Final calculation
  rw [h14] at h13
  linarith