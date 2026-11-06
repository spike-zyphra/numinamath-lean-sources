import Mathlib


lemma int_ceil_iff {a : ℤ} {b : ℝ}: a = ⌈b⌉ ↔ a - 1 < b ∧ b ≤ a := by
  constructor
  · -- Assume a = ⌈b⌉, prove a - 1 < b ∧ b ≤ a
    intro h_eq
    have h1 : (a : ℝ) = (⌈b⌉ : ℝ) := by exact_mod_cast h_eq
    have h2 : b ≤ (a : ℝ) := by
      have h3 : b ≤ (⌈b⌉ : ℝ) := by apply Int.le_ceil
      rw [show (⌈b⌉ : ℝ) = (a : ℝ) by linarith [h1]] at h3
      linarith
    have h3 : (a : ℝ) - 1 < b := by
      have h4 : (⌈b⌉ : ℝ) < b + 1 := by
        apply Int.ceil_lt_add_one
      have h5 : (⌈b⌉ : ℝ) - 1 < b := by
        linarith
      have h6 : (a : ℝ) - 1 < b := by
        have h7 : (⌈b⌉ : ℝ) - 1 < b := h5
        have h8 : (a : ℝ) = (⌈b⌉ : ℝ) := by linarith [h1]
        rw [h8] at *
        linarith
      linarith
    constructor
    · exact h3
    · exact h2
  · -- Assume a - 1 < b ∧ b ≤ a, prove a = ⌈b⌉
    rintro ⟨h1, h2⟩
    have h3 : a ≥ ⌈b⌉ := by
      by_contra h
      push_neg at h
      have h6 : a < (⌈b⌉ : ℤ) := by omega
      have h7 : a ≤ (⌈b⌉ - 1 : ℤ) := by omega
      have h8 : (a : ℝ) ≤ ((⌈b⌉ - 1 : ℤ) : ℝ) := by exact_mod_cast h7
      have h11 : (a : ℝ) ≤ (⌈b⌉ - 1 : ℝ) := by
        have h12 : (a : ℝ) ≤ ((⌈b⌉ - 1 : ℤ) : ℝ) := by exact_mod_cast h7
        norm_num at h12 ⊢
        all_goals nlinarith
      have h13 : (⌈b⌉ - 1 : ℝ) < (b : ℝ) := by
        have h14 : (⌈b⌉ : ℝ) < (b + 1 : ℝ) := by
          apply Int.ceil_lt_add_one
        linarith
      have h14 : (a : ℝ) < (b : ℝ) := by
        nlinarith
      nlinarith
    have h15 : a ≤ (⌈b⌉ : ℤ) := by
      by_contra h
      push_neg at h
      have h16 : a > (⌈b⌉ : ℤ) := by omega
      have h17 : a ≥ (⌈b⌉ + 1 : ℤ) := by omega
      have h17 : (a : ℝ) ≥ ((⌈b⌉ + 1 : ℤ) : ℝ) := by exact_mod_cast h17
      have h19 : (b : ℝ) ≤ (⌈b⌉ : ℝ) := by apply Int.le_ceil
      have h20 : (⌈b⌉ : ℝ) + 1 ≤ (a : ℝ) := by
        have h21 : ((⌈b⌉ + 1 : ℤ) : ℝ) ≤ (a : ℝ) := by linarith [h17]
        have h22 : ((⌈b⌉ + 1 : ℤ) : ℝ) = (⌈b⌉ : ℝ) + 1 := by simp
        linarith
      have h23 : (a : ℝ) - 1 ≥ (⌈b⌉ : ℝ) := by
        nlinarith
      have h24 : (a : ℝ) - 1 < (b : ℝ) := by linarith
      nlinarith
    have h16 : a = (⌈b⌉ : ℤ) := by omega
    exact_mod_cast h16

theorem my_favorite_theorem (m X : ℕ)
  (h1 : (∑ i ∈ Finset.range (m + 1), i) ≤ X)
  (h2 : X < (∑ i ∈ Finset.range (m + 2), i)) :
    m = ⌈(Real.sqrt (8 * X + 9) - 3) / 2⌉ := by

  rw [Finset.sum_range_id] at h1 h2
  replace h1 : (m + 1) * m / 2 < X + 1 := by simp at h1; omega
  replace h2 : X + 1 ≤ (m + 2) * (m + 1) / 2 := by simp at h2; omega


  rw [int_ceil_iff]
  constructor
  . suffices 2*m+1<√(8*X+9) by
      push_cast
      linarith

    rw [Real.lt_sqrt (by norm_cast; omega)]
    norm_cast
    suffices (m + 1) * m < 2 * (X + 1) by linarith
    omega

  . suffices √(8*X+9) ≤ 2*m+3 by
      push_cast
      linarith

    rw [Real.sqrt_le_iff]
    constructor
    . norm_cast
      omega
    . norm_cast
      suffices (X + 1) * 2 ≤ (m + 2) * (m + 1) by linarith
      omega
