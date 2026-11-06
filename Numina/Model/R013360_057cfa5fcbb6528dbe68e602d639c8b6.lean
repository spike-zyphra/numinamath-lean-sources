import Mathlib

theorem algebra_11886 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (hpos : ∀ n, b n > 0)
    (h1 : a 2 = 5) (h2 : a 8 = 23) (h3 : b 1 = 2) (h4 : ∀ s t, b (s + t) = b s * b t) :
    ∀ n, a n = 3 * n - 1 ∧ b n = 2 ^ n := by
  rcases ha with ⟨d, had⟩
  have eq1 : a 2 = a 0 + 2 * d := by
    rw [had 2]
    ring
  have eq2 : a 8 = a 0 + 8 * d := by
    rw [had 8]
    ring
  rw [eq1] at h1
  rw [eq2] at h2
  have ha0 : a 0 = -1 := by 
    linarith
  have hd : d = 3 := by
    linarith
  rcases hb with ⟨r, hbl⟩
  have eq2 : b 1 = b 0 * r ^ 1 := hbl 1
  rw [h3] at eq2
  have eq3 : b 2 = b 1 * b 1 := by
    specialize h4 1 1
    simpa using h4
  rw [h3] at eq3
  have eq4 : b 2 = b 0 * r ^ 2 := hbl 2
  have eq5 : b 0 * r = 2 := by
    nlinarith
  have eq6 : b 0 * r ^ 2 = 4 := by
    nlinarith [eq3, eq4]
  have h_r : r = 2 := by
    nlinarith [hpos 0, hpos 1, hpos 2, sq_nonneg (b 0 - 1), sq_nonneg (r - 2)]
  have h_b0 : b 0 = 1 := by
    rw [h_r] at eq5
    nlinarith [hpos 0]
  intro n 
  constructor
  · -- proof for $a_n = 3n - 1$.
    have ha3 : ∀ n : ℕ, a n = 3 * n - 1 := by 
      intro n
      have h : a n = a 0 + d * n := had n
      rw [h, ha0, hd]
      all_goals ring_nf <;> linarith
    exact ha3 n
  · -- proof for $b_n = 2^n$.
    have hb3 : ∀ n : ℕ, b n = 2 ^ n := by
      intro n 
      have h7 : b n = b 0 * r ^ n := hbl n
      rw [h7, h_b0, h_r]
      <;> simp
    exact hb3 n