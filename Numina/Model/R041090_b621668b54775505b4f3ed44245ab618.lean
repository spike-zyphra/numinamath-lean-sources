import Mathlib

theorem algebra_602044 {a b c : ℝ} (ha : |a * 0 ^ 2 + b * 0 + c| ≤ 1)
    (hb : |c * 1 ^ 2 + b * 1 + a| ≤ 1) (hc : |c * (-1) ^ 2 + b * (-1) + a| ≤ 1)
    (F G : ℝ → ℝ) (hF : F = fun x => a * x ^ 2 + b * x + c)
    (hG : G = fun x => c * x ^ 2 + b * x + a) :
    ∀ x, |x| ≤ 1 → |F x| ≤ 5 / 4 ∧ |G x| ≤ 2 := by 
  have ha1 : -1 ≤ c := by 
    norm_num [abs_le] at ha 
    linarith 
  have ha2 : c ≤ 1 := by 
    norm_num [abs_le] at ha 
    linarith 
  have hb1 : -1 ≤ a + b + c := by 
    norm_num [abs_le] at hb 
    linarith 
  have hb2 : a + b + c ≤ 1 := by 
    norm_num [abs_le] at hb 
    linarith 
  have hc1 : -1 ≤ a - b + c := by 
    norm_num [abs_le] at hc 
    linarith 
  have hc2 : a - b + c ≤ 1 := by 
    norm_num [abs_le] at hc 
    linarith 
  -- Now, we can derive bounds for a, b, c.
  have h3 : -2 ≤ a := by 
    nlinarith 
  have h4 : a ≤ 2 := by 
    nlinarith 
  have h5 : -1 ≤ b := by
    nlinarith 
  have h6 : b ≤ 1 := by 
    nlinarith 
  intro x hx 
  have hx1 : -1 ≤ x := by 
    linarith [abs_le.mp hx]
  have hx2 : x ≤ 1 := by 
    linarith [abs_le.mp hx]
  have hx3 : x ^ 2 ≤ 1 := by
    nlinarith 
  have h7 : -5 / 4 ≤ a * x ^ 2 + b * x + c := by 
    by_cases h8 : x ≥ 0 
    · -- If x ≥ 0, then x ∈ [0, 1].
      by_cases h9 : x ≤ 1 / 2 
      · -- x ∈ [0, 1/2]
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x - 1 / 2) * a), sq_nonneg ((x - 1 / 2) * b), sq_nonneg ((x - 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
      · -- x ∈ (1/2, 1]
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x - 1 / 2) * a), sq_nonneg ((x - 1 / 2) * b), sq_nonneg ((x - 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
    · -- If x < 0, then x ∈ [-1, 0).
      by_cases h9 : x ≥ -1 / 2 
      · -- x ∈ [-1/2, 0)
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x + 1 / 2) * a), sq_nonneg ((x + 1 / 2) * b), sq_nonneg ((x + 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ -x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
      · -- x ∈ [-1, -1/2)
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x + 1 / 2) * a), sq_nonneg ((x + 1 / 2) * b), sq_nonneg ((x + 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ -x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
  -- Prove F(x) ≤ 5/4
  have h8 : a * x ^ 2 + b * x + c ≤ 5 / 4 := by 
    by_cases h8 : x ≥ 0 
    · -- If x ≥ 0, then x ∈ [0, 1].
      by_cases h9 : x ≤ 1 / 2 
      · -- x ∈ [0, 1/2]
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x - 1 / 2) * a), sq_nonneg ((x - 1 / 2) * b), sq_nonneg ((x - 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
      · -- x ∈ (1/2, 1]
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x - 1 / 2) * a), sq_nonneg ((x - 1 / 2) * b), sq_nonneg ((x - 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
    · -- If x < 0, then x ∈ [-1, 0).
      by_cases h9 : x ≥ -1 / 2 
      · -- x ∈ [-1/2, 0)
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x + 1 / 2) * a), sq_nonneg ((x + 1 / 2) * b), sq_nonneg ((x + 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ -x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
      · -- x ∈ [-1, -1/2)
        nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg ((x + 1 / 2) * a), sq_nonneg ((x + 1 / 2) * b), sq_nonneg ((x + 1 / 2) * (x)), mul_nonneg (show (0 : ℝ) ≤ -x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
  have h9 : -2 ≤ c * x ^ 2 + b * x + a := by 
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg ((c * (x)) - (b / 2)), sq_nonneg ((a) - (c * (x^2))), sq_nonneg ((b) - (c * (x))), mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith), mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  -- Prove G(x) ≤ 2
  have h10 : c * x ^ 2 + b * x + a ≤ 2 := by 
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg ((c * (x)) - (b / 2)), sq_nonneg ((a) - (c * (x^2))), sq_nonneg ((b) - (c * (x))), mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith), mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  -- Now, use these bounds and `abs_le` to establish the goals.
  have h7' : F x = a * x ^ 2 + b * x + c := by 
    rw [hF]
  have h8' : G x = c * x ^ 2 + b * x + a := by 
    rw [hG]
  have h11 : -5 / 4 ≤ F x := by 
    rw [h7']
    linarith 
  have h12 : F x ≤ 5 / 4 := by 
    rw [h7']
    linarith 
  have h13 : -2 ≤ G x := by 
    rw [h8']
    linarith 
  have h14 : G x ≤ 2 := by 
    rw [h8']
    linarith 
  constructor
  · -- Show |F x| ≤ 5 / 4
    apply abs_le.mpr 
    constructor <;> linarith 
  · -- Show |G x| ≤ 2 
    apply abs_le.mpr 
    constructor <;> linarith