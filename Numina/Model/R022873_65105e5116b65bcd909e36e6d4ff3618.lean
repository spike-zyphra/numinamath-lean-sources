import Mathlib

theorem algebra_103269 (a b : ℕ → ℝ) (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (ha0 : a 0 = 25) (hb0 : b 0 = 75)
    (h100 : a 99 + b 99 = 100) :
    ∑ i in Finset.range 100, (a i + b i) = 10000 := by 
  rcases ha with ⟨d, had⟩
  rcases hb with ⟨d', hdb⟩
  have ha99 : a 99 = a 0 + 99 * d := by
    have h1 : ∀ (n : ℕ), a n = a 0 + d * (n : ℝ) := by 
      intro n
      specialize had n
      simpa using had
    specialize h1 99
    norm_num at h1 ⊢
    linarith
  have hb99 : b 99 = b 0 + 99 * d' := by 
    have h1 : ∀ (n : ℕ), b n = b 0 + d' * (n : ℝ) := by 
      intro n
      specialize hdb n 
      simpa using hdb 
    specialize h1 99
    norm_num at h1 ⊢ 
    linarith 
  have h3 : d + d' = 0 := by 
    rw [ha99, hb99, ha0, hb0] at h100
    ring_nf at h100
    linarith
  have hn1 : ∀ (n : ℕ), a n = 25 + (n : ℝ) * d := by
    intro n
    specialize had n 
    rw [ha0] at had
    linarith
  have hn5' : ∀ (n : ℕ), b n = 75 + (n : ℝ) * d' := by 
    intro n 
    specialize hdb n
    rw [hb0] at hdb 
    linarith 
  have h5 : ∀ (i : ℕ), a i + b i = 100 := by 
    intro i 
    have ha1 : a i = 25 + (i : ℝ) * d := by 
      apply hn1 
    have hb1 : b i = 75 + (i : ℝ) * d' := by 
      apply hn5' 
    rw [ha1, hb1]
    have h4' : d + d' = 0 := h3 
    ring_nf at *
    <;> nlinarith 
  have eq3 : ∑ i in Finset.range 100, (a i + b i) = 10000 := by
    have eq1 : ∀ (i : ℕ), a i + b i = 100 := h5
    have eq2 : ∑ i in Finset.range 100, (a i + b i) = 10000 := by
      have eq1' : ∀ (i : ℕ), a i + b i = (100 : ℝ) := h5 
      have eq11 : ∑ i in Finset.range 100, (a i + b i) = (100 : ℝ) * (100 : ℝ) := by 
        rw [Finset.sum_congr rfl (fun i _ => eq1' i)]
        simp
        <;> norm_num
      rw [eq11]
      all_goals norm_num 
    linarith 
  exact_mod_cast eq3