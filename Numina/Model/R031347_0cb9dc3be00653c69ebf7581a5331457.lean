import Mathlib

theorem algebra_127117 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : 3 * a 8 = 5 * a 13)
    (ha1 : a 1 > 0) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i) :
    IsGreatest {x | ∃ n, x = S n ∧ n ≤ 20} (S 20) := by 
  rcases ha with ⟨d, had⟩
  have eq1 : a 8 = a 0 + (d * 8) := by 
    specialize had 8
    norm_num at had ⊢
    linarith
  have eq2 : a 13 = a 0 + (d * 13) := by 
    specialize had 13
    norm_num at had ⊢
    linarith
  have eq3 : 3 * (a 0 + (d * 8)) = 5 * (a 0 + (d * 13)) := by
    rw [eq1] at h
    rw [eq2] at h
    linarith
  have eq4 : a 1 = a 0 + d := by
    specialize had 1
    norm_num at had ⊢
    linarith
  have ha0 : a 0 + d > 0 := by
    linarith [ha1, eq4]
  constructor
  · -- Show that S 20 is in the set.
    use 20
    all_goals norm_num
  · -- Show that S 20 is the greatest.
    intro x hx
    rcases hx with ⟨n, hn1, hn2⟩
    have h3 : n ≤ 20 := hn2
    have h4 : x = S n := by linarith [hn1]
    rw [h4]
    have h5 : n ≤ 20 := h3
    have h6 : ∀ (n : ℕ), n ≤ 20 → S 20 ≥ S n := by
      intro n hn
      rw [hS 20, hS n]
      have h5 : n ≤ 20 := hn
      have eq7 : ∑ i in Finset.range 20, a i = 20 * a 0 + (190 : ℝ) * d := by
        have h1 : ∀ (i : ℕ), i ∈ Finset.range 20 → a i = a 0 + (d * (i : ℝ)) := by 
          intro i hi
          have h8 : i < 20 := by 
            simp at hi ⊢
            linarith
          have h9 : a i = a 0 + (d * (i : ℝ)) := by 
            specialize had i
            simpa using had
          tauto
        rw [Finset.sum_congr rfl (fun i hi => h1 i hi)]
        norm_num [Finset.sum_range_succ]
        <;> ring
      have eq8 : ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + (( (n : ℝ) * ( (n : ℝ) - 1 ) ) / 2 ) * d := by
        have h1 : ∀ (i : ℕ), i ∈ Finset.range n → a i = a 0 + (d * (i : ℝ)) := by
          intro i hi
          have h9 : i < n := by 
            simp at hi ⊢
            linarith
          have h10 : a i = a 0 + (d * (i : ℝ)) := by 
            specialize had i
            simpa using had
          tauto
        rw [Finset.sum_congr rfl (fun i hi => h1 i hi)]
        have h5 : ∀ (n : ℕ), ∑ i in Finset.range n, (a 0 + (d * (i : ℝ)) ) = (n : ℝ) * a 0 + (( (n : ℝ) * ( (n : ℝ) - 1  ) ) / 2 ) * d := by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [Finset.sum_range_succ, ih]
            field_simp at *
            ring
        specialize h5 n
        simpa using h5
      have eq9 : (20 : ℝ) * a 0 + (190 : ℝ) * d ≥ (n : ℝ) * a 0 + (( (n : ℝ) * ( (n : ℝ) - 1 ) ) / 2 ) * d := by 
        have h9 : a 0 = -41 / 2 * d := by 
          nlinarith 
        rw [h9]
        have h9 : d < (0 : ℝ) := by 
          nlinarith [ha1, h9, had 1, eq4, ha0]
        interval_cases n <;> norm_num at *
        <;> nlinarith
      linarith [eq7, eq8, eq9]
    have h7 : x ≤ S 20 := by
      have eq10 : S 20 ≥ S n := h6 n (by omega)
      nlinarith [eq10, h4]
    linarith