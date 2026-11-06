import Mathlib

theorem algebra_20639 (total_pages : ℕ) (words_per_page : ℕ) (reading_rate : ℕ)
    (h₀ : total_pages = 420) (h₁ : words_per_page = 600) (h₂ : reading_rate = 360) :
    total_pages * words_per_page / (60 * reading_rate) =(11 + 2 / 3 : ℝ):= by
  rw [h₀, h₁, h₂]
  norm_num