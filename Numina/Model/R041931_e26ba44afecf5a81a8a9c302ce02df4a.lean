import Mathlib

theorem algebra_301579 {a b c : ℝ} (habc : a * b * c ≠ 0) (h1 : a + b + c = 2) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 2) :
    (1 - a) ^ 2 / (b * c) + (1 - b) ^ 2 / (c * a) + (1 - c) ^ 2 / (a * b) = 3 := by
  have h3 : a * b + b * c + c * a = 1 := by
    have h : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h1, h2] at h
    linarith
  have h4 : a ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  have h5 : b ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  have h6 : c ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  have h7 : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by ring
  have h8 : a ^ 3 + b ^ 3 + c ^ 3 = 2 + 3 * (a * b * c) := by
    rw [h7, h1, h3]
    nlinarith
  have h9 : (1 - a) ^ 2 / (b * c) + (1 - b) ^ 2 / (c * a) + (1 - c) ^ 2 / (a * b) =
      ( a * (1 - a) ^ 2 + b * (1 - b) ^ 2 + c * (1 - c) ^ 2 ) / (a * b * c) := by
    field_simp [show b * c ≠ 0 by
      by_contra h
      have : b = 0 ∨ c = 0 := by
        by_cases hb : b = 0
        · left
          exact hb
        · right
          have : c = 0 := by
            apply_fun (fun x => x / b) at h
            field_simp [hb] at h ⊢
            all_goals nlinarith
          exact this
      cases this with
      | inl hb =>
        rw [hb] at habc
        simp at habc
      | inr hc =>
        rw [hc] at habc
        simp at habc
        ]
    <;> ring_nf <;> field_simp [show b ≠ 0 by exact h5, show c ≠ 0 by exact h6, show a ≠ 0 by exact h4] <;> ring
  have h10 : a * (1 - a) ^ 2 + b * (1 - b) ^ 2 + c * (1 - c) ^ 2 = 3 * (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h8]
  rw [h9]
  rw [h10]
  have h11 : a * b * c ≠ 0 := habc
  field_simp [h11]
  <;> ring_nf <;> field_simp [h11] <;> nlinarith