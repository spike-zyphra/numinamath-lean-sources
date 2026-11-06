import Mathlib

theorem algebra_8328 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (h1 : a 1 = b 1) (h2 : a 2 = 5)
    (h3 : a 3 = 4 * a 1) (h4 : a 3 = 2 * b 2) :
    ∀ n, a n = 3 * n - 1 ∧ b n = 2 ^ n := by
  rcases ha with ⟨d, had⟩
  rcases hb with ⟨r, hbl⟩
  have eq1 : a 1 = a 0 + d := by
    specialize had 1
    norm_num at had 
    linarith
  have eq2 : a 2 = a 0 + 2 * d := by
    specialize had 2
    norm_num at had 
    linarith
  have eq3 : a 3 = a 0 + 3 * d := by
    specialize had 3
    norm_num at had 
    linarith
  have eq6 : b 1 = b 0 * r ^ 1 := hbl 1
  have eq7 : b 2 = b 0 * r ^ 2 := hbl 2
  rw [eq1] at h1
  rw [eq6] at h1
  rw [eq2] at h2
  rw [eq3] at h3
  rw [eq1] at h3
  rw [eq3] at h4
  rw [eq7] at h4
  have h5 : d = 3 := by
    nlinarith
  have h6 : a 0 = -1 := by
    nlinarith
  have hb2 : r = (2 : ℝ) := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (b 0 - 1)]
  have hb2b : b 0 = (1 : ℝ) := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (b 0 - 1)]
  have h7 : ∀ n, a n = 3 * n - 1 := by
    intro n 
    have eq11 : a n = a 0 + (d) * (n : ℝ) := by 
      specialize had n 
      simpa using had
    rw [eq11, h6, h5]
    ring_nf
  have hb3 : ∀ n, b n = 2 ^ n := by
    intro n 
    have eq12 : b n = b 0 * (r) ^ (n : ℕ) := by 
      specialize hbl n 
      simpa using hbl
    rw [eq12, hb2b, hb2]
    simp
  intro n
  constructor
  · -- Show that the arithmetic sequence is correct
    specialize h7 n 
    simpa using h7
  · -- Show that the geometric sequence is correct
    specialize hb3 n 
    simpa using hb3