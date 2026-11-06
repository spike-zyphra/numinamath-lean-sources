import Mathlib

theorem algebra_63270 (x y z : ℝ) (hx : x^2 = y + 2) (hy : y^2 = z + 2) (hz : z^2 = x + 2) :
    ∃ n : ℤ, x + y + z = n := by
  let S := x + y + z
  have h₀ : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) + 6 := by
    linarith
  have h₁ : (x * y * z) ^ 2 = (x + 2) * (y + 2) * (z + 2) := by
    calc
      _ = z ^ 2 * x ^ 2 * y ^ 2 := by ring
      _ = (x + 2) * (y + 2) * (z + 2) := by rw [hx, hy, hz]
  have h₂ : S ^ 2 - S - 6 = 2 * (x * y + y * z + z * x) := by
    unfold S
    linarith
  have h₃ : (S ^ 2 - S - 6) ^ 2 = 2 * (S ^ 2 - S - 6) + 16 * S + 48 + 8 * (x * y * z) * S := by
    calc
      _ = (2 * (x * y + y * z + z * x)) ^ 2 := by rw [h₂]
      _ = 4 * ((y + 2) * (z + 2) + (z + 2) * (x + 2) + (x + 2) * (y + 2) + 2 * (x * y * z) * (x + y + z)) := by
        rw [<-hx, <-hy, <-hz]
        ring
      _ = 2 * (2 * (x * y + y * z + z * x)) + 16 * (x + y + z) + 48 + 8 * (x * y * z) * (x + y + z) := by ring
      _ = 2 * (S ^ 2 - S - 6) + 16 * S + 48 + 8 * (x * y * z) * S := by
        unfold S
        rw [<-h₂]
  have h₄ : (x * y * z) ^ 2 = x * y * z + S ^ 2 + 3 * S + 2 := by
    calc
      _ = (x + 2) * (y + 2) * (z + 2) := h₁
      _ = x * y * z + (S ^ 2 - S - 6) + 4 * S + 8 := by
        rw [h₂]
        unfold S
        ring
      _ = x * y * z + S ^ 2 + 3 * S + 2 := by ring
  replace h₄ := congr_arg (· * (64 * S ^ 2)) h₄
  simp only at h₄
  replace h₄ : (8 * (x * y * z) * S - 4 * S) ^ 2 = (8 * S ^ 2 + 12 * S) ^ 2 := by linarith only [h₄]
  have h₅ : ((S ^ 2 - S - 6) ^ 2 - 2 * (S ^ 2 - S - 6) - 16 * S - 48 - 4 * S) ^ 2 = (8 * S ^ 2 + 12 * S) ^ 2 := by
    calc
      _ = (8 * (x * y * z) * S - 4 * S) ^ 2 := by
        congr
        linarith only [h₃]
      _ = (8 * S ^ 2 + 12 * S) ^ 2 := h₄
  replace h₅ : S ^ 2 * (S + 3) * (S + 2) * (S + 1) * (S - 1) * (S - 3) * (S - 6) = 0 := by
    linarith only [h₅]
  simp at h₅
  rcases h₅ with ((((((h₅ | h₅) | h₅) | h₅) | h₅) | h₅) | h₅)
  <;> [use 0; use -3; use -2; use -1; use 1; use 3; use 6]
  all_goals
    simp [S] at h₅ ⊢
    linarith only [h₅]