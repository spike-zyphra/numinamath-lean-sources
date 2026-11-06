import Mathlib

theorem algebra_183089 (a b c : ℕ → ℝ) (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (hc : ∀ n, c n = a n * b n)
    (h1 : c 1 = 1440) (h2 : c 2 = 1716) (h3 : c 3 = 1848) :
    c 8 = 348 := by
  rcases ha with ⟨d_a, ha_n⟩
  rcases hb with ⟨d_b, hb_n⟩
  have eq1 : c 1 = a 1 * b 1 := by apply hc
  have eq2 : c 2 = a 2 * b 2 := by apply hc
  have eq3 : c 3 = a 3 * b 3 := by apply hc
  have eq8 : c 8 = a 8 * b 8 := by apply hc

  have ha1 : a 1 = a 0 + d_a * (1 : ℕ) := by apply ha_n
  have ha2 : a 2 = a 0 + d_a * (2 : ℕ) := by apply ha_n
  have ha3 : a 3 = a 0 + d_a * (3 : ℕ) := by apply ha_n
  have ha8 : a 8 = a 0 + d_a * (8 : ℕ) := by apply ha_n

  have hb1 : b 1 = b 0 + d_b * (1 : ℕ) := by apply hb_n
  have hb2 : b 2 = b 0 + d_b * (2 : ℕ) := by apply hb_n
  have hb3 : b 3 = b 0 + d_b * (3 : ℕ) := by apply hb_n
  have hb8 : b 8 = b 0 + d_b * (8 : ℕ) := by apply hb_n

  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h3
  rw [eq8] at *

  rw [ha1] at h1
  rw [ha2] at h2
  rw [ha3] at h3
  rw [ha8] at *

  rw [hb1] at h1
  rw [hb2] at h2
  rw [hb3] at h3
  rw [hb8] at *

  norm_num at h1 h2 h3 ⊢
  nlinarith [h1, h2, h3, sq_nonneg (a 0 - b 0), sq_nonneg (d_a - d_b), sq_nonneg (a 0 + b 0), sq_nonneg (d_a + d_b)]