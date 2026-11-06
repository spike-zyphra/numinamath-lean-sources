import Mathlib

theorem algebra_8329 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (h1 : a 0 = b 0) (h2 : a 1 = 5) (h3 : a 2 = 4 * a 0) (h4 : a 2 = 2 * b 1) :
    ∑ i in Finset.range n, a i * b i = 8 + 2 ^ (n + 1) * (3 * n - 4) := by
  rcases ha with ⟨d, had⟩
  rcases hb with ⟨r, hbl⟩
  have ha1 : a 1 = a 0 + d := by
    specialize had 1
    norm_num at had
    linarith
  have ha2 : a 2 = a 0 + 2 * d := by
    specialize had 2
    norm_num at had
    linarith
  have ha0_eq : a 0 = 2 := by
    nlinarith [h3, ha1, ha2]
  have h1' : d = 3 := by
    linarith [h2, ha1, ha0_eq]
  have ha_n : ∀ n, a n = 2 + 3 * (n : ℝ) := by
    intro n
    specialize had n
    rw [ha0_eq, h1'] at had
    linarith
  have hb0_eq : b 0 = 2 := by
    nlinarith [h1, ha0_eq]
  have hb1_eq' : b 1 = (b 0 * r : ℝ) := by
    specialize hbl 1
    simpa using hbl
  have ha2' : a 2 = 8 := by
    rw [ha_n 2]
    norm_num
  have hr_eq : r = 2 := by
    nlinarith [h4, ha2', hb1_eq', hb0_eq]
  have hb1_eq : b 1 = 4 := by
    rw [hb0_eq, hr_eq] at hb1_eq'
    linarith
  have hb_n : ∀ n, b n = 2 * (2 : ℝ) ^ n := by
    intro n
    specialize hbl n
    rw [hb0_eq, hr_eq] at hbl
    linarith
  have h6 : ∀ (n : ℕ), ∑ i in Finset.range n, a i * b i = 8 + 2 ^ (n + 1) * (3 * n - 4) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> linarith
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [ha_n, hb_n]
      field_simp at *
      ring_nf
  specialize h6 n
  simpa using h6