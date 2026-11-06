import Mathlib

theorem algebra_12882 (a : ℕ → ℤ) (h₀ : ∀ n, 0 < n → a (n + 2) = 6 * a n + a (n + 1))
    (h₁ : a 1 = 1) (h₂ : a 2 = 2) :
    a 10 - 3 * a 9 = -256 := by
  have h₃ : a 3 = 6 * a 1 + a 2 := h₀ 1 (by norm_num)
  rw [h₁, h₂] at h₃
  norm_num at h₃ -- a 3 = 8

  have h₄ : a 4 = 6 * a 2 + a 3 := h₀ 2 (by norm_num)
  rw [h₂, h₃] at h₄
  norm_num at h₄ -- a 4 = 20

  have h₅ : a 5 = 6 * a 3 + a 4 := h₀ 3 (by norm_num)
  rw [h₃, h₄] at h₅
  norm_num at h₅ -- a 5 = 68

  have h₆ : a 6 = 6 * a 4 + a 5 := h₀ 4 (by norm_num)
  rw [h₄, h₅] at h₆
  norm_num at h₆ -- a 6 = 188

  have h₇ : a 7 = 6 * a 5 + a 6 := h₀ 5 (by norm_num)
  rw [h₅, h₆] at h₇
  norm_num at h₇ -- a 7 = 596

  have h₈ : a 8 = 6 * a 6 + a 7 := h₀ 6 (by norm_num)
  rw [h₆, h₇] at h₈
  norm_num at h₈ -- a 8 = 1724

  have h₉ : a 9 = 6 * a 7 + a 8 := h₀ 7 (by norm_num)
  rw [h₇, h₈] at h₉
  norm_num at h₉ -- a 9 = 5300

  have h₁₀ : a 10 = 6 * a 8 + a 9 := h₀ 8 (by norm_num)
  rw [h₈, h₉] at h₁₀
  norm_num at h₁₀ -- a 10 = 15644

  rw [h₁₀, h₉]
  norm_num -- compute a 10 - 3 * a 9 = 15644 - 3 * 5300 = 15644 - 15900 = -256