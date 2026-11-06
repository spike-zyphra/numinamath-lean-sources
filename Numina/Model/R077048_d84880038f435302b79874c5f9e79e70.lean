import Mathlib

theorem algebra_267327 : ∑ᶠ x ∈ {x : ℝ | x ^ 256 - 256 ^ 32 = 0}, x ^ 2 = 8 := by

  have eq1 : ∀ x : ℝ, x ^ 256 - 256 ^ 32 = 0 ↔ x = 2 ∨ x = -2 := by
    intro x
    constructor
    · -- Forward direction: if x^256 - 256^32 = 0, then x = 2 or x = -2
      intro h
      have h1 : x ^ 256 = (256 : ℝ) ^ 32 := by linarith
      have h2 : (256 : ℝ) ^ 32 = (2 : ℝ) ^ 256 := by
        norm_num
      rw [h2] at h1
      have h3 : x^2 = 4 := by
        have h4 : (x ^ 2) ^ 128 = ((2:ℝ) ^ 2) ^ 128 := by
          calc
            (x ^ 2) ^ 128 = x ^ 256 := by ring_nf
            _ = (2 : ℝ) ^ 256 := by linarith [h1]
            _ = ((2 : ℝ) ^ 2) ^ 128 := by ring_nf
        have h5 : x ^ 2 = (2 : ℝ) ^ 2 := by
          rw [pow_left_inj] at h4
          · nlinarith
          all_goals nlinarith
          all_goals linarith
        norm_num at h5 ⊢
        linarith
      have h4 : x = 2 ∨ x = -2 := by
        have h5 : x^2 - 4 = 0 := by linarith
        have h6 : (x - 2) * (x + 2) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h6) with
        | inl h7 =>
          left
          linarith
        | inr h8 =>
          right
          linarith
      tauto
    · -- Backward direction: if x = 2 or x = -2, then x^256 - 256^32 = 0
      rintro (h | h)
      · -- Case x = 2
        rw [h]
        norm_num
      · -- Case x = -2
        rw [h]
        norm_num

  have h2 : {x : ℝ | x ^ 256 - 256 ^ 32 = 0} = {2, -2} := by
    ext x
    simp [eq1]
    <;> tauto

  rw [h2]
  rw [finsum_mem_pair (by norm_num)]
  norm_num
  all_goals norm_num