import Mathlib

theorem algebra_175585 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (ha0 : a 0 = 25) (hb0 : b 0 = 75)
    (han : a 99 + b 99 = 100) :
    ∑ i in Finset.range 100, (a i + b i) = 10000 := by
  rcases ha with ⟨da, hada⟩
  rcases hb with ⟨db, hdb⟩
  have ha99 : a 99 = a 0 + da * (99 : ℕ) := by
    specialize hada 99
    simpa using hada
  have hb99 : b 99 = b 0 + db * (99 : ℕ) := by
    specialize hdb 99
    simpa using hdb
  rw [ha99, hb99, ha0, hb0] at han
  have h1 : da + db = 0 := by
    norm_num at han
    linarith
  have h2 : ∀ i : ℕ, a i + b i = 100 := by
    intro i
    have ha_i : a i = a 0 + da * (i : ℕ) := by
      specialize hada i
      simpa using hada
    have hb_i : b i = b 0 + db * (i : ℕ) := by
      specialize hdb i
      simpa using hdb
    rw [ha_i, hb_i, ha0, hb0]
    have h4 : (da : ℝ) * (i : ℝ) + (db : ℝ) * (i : ℝ) = 0 := by
      have h5 : (da : ℝ) + (db : ℝ) = 0 := by
        linarith [h1]
      have h6 : (da : ℝ) * (i : ℝ) + (db : ℝ) * (i : ℝ) = (da + db) * (i : ℝ) := by
        ring
      rw [h6, h5]
      norm_num
      all_goals linarith
    linarith [h4]
  have h5 : ∑ i in Finset.range 100, (a i + b i) = 10000 := by
    have h6 : ∀ i : ℕ, a i + b i = 100 := h2
    have h7 : ∑ i in Finset.range 100, (a i + b i) = ∑ i in Finset.range 100, (100 : ℝ) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have h8 : a i + b i = (100 : ℝ) := h6 i
        simpa using h8
    rw [h7]
    norm_num [Finset.sum_range_succ]
  exact h5