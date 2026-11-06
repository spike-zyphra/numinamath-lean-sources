import Mathlib


theorem algebra_303742 (a : ℕ → ℝ) (h : ∃ d, ∀ n, a n = a 0 + d * n)
    (ha : a 0 > 0) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i)
    (hS1 : S 3 = S 11) :
    IsGreatest {x | ∃ n, x = S n} (S 7) := by
  rcases h with ⟨d, had⟩
  have h3 : S 3 = 3 * a 0 + 3 * d := by
    rw [hS 3]
    simp [Finset.sum_range_succ, had 1, had 2]
    ring
  have h11 : S 11 = 11 * a 0 + 55 * d := by
    rw [hS 11]
    norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9, had 10]
    ring
  have h_eq : 2 * a 0 + 13 * d = 0 := by
    linarith [h3, h11, hS1]
  have h8 : d < 0 := by
    nlinarith [show 2 * a 0 + 13 * d = 0 by linarith, ha]
  have hSn : ∀ (n : ℕ), S n = (n : ℝ) * a 0 + (d * ((n : ℝ) * ((n : ℝ) - 1) / 2)) := by
    intro n
    rw [hS n]
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have eq1 : ∑ i in Finset.range (n + 1), a i = ∑ i in Finset.range n, a i + a n := by
        rw [Finset.sum_range_succ]
      rw [eq1]
      rw [ih]
      have eq2 : a n = a 0 + (d : ℝ) * (n : ℝ) := by
        specialize had n
        simpa using had
      simp [eq2]
      ring_nf
  constructor
  · -- Show that S 7 is in the set
    use 7
  · -- Show that S 7 is the greatest
    intro x hx
    rcases hx with ⟨n, hn⟩
    have h7 : x = S n := by linarith
    have h4 : S 7 ≥ S n := by
      have hS7 : S 7 = 7 * a 0 + 21 * d := by
        rw [hSn 7]
        ring_nf
      have hSn' : S n = (n : ℝ) * a 0 + (d * ((n : ℝ) * ((n : ℝ) - 1) / 2)) := hSn n
      rw [hS7, hSn']
      have ha_eq : a 0 = -13 / 2 * d := by
        linarith [show 2 * a 0 + 13 * d = 0 by linarith [h_eq]]
      rw [ha_eq]
      have h8 : d < 0 := by linarith
      have h13 : (7 : ℝ) * (-13 / 2 * d) + 21 * d ≥ (n : ℝ) * (-13 / 2 * d) + d * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
        have h14 : (7 : ℝ) * (-13 / 2 * d) + 21 * d - ((n : ℝ) * (-13 / 2 * d) + d * ((n : ℝ) * ((n : ℝ) - 1) / 2)) ≥ 0 := by
          have h15 : (7 : ℝ) * (-13 / 2 * d) + 21 * d - ((n : ℝ) * (-13 / 2 * d) + d * ((n : ℝ) * ((n : ℝ) - 1) / 2)) = d * ((7 * (-13 / 2 : ℝ) + 21) - (n * (-13 / 2 : ℝ) + ((n : ℝ) * ((n : ℝ) - 1) / 2))) := by ring
          rw [h15]
          have h16 : d < 0 := by linarith
          have h17 : (7 * (-13 / 2 : ℝ) + 21) - (n * (-13 / 2 : ℝ) + ((n : ℝ) * ((n : ℝ) - 1) / 2)) ≤ 0 := by
            nlinarith [sq_nonneg ((n : ℝ) - 7 : ℝ), sq_nonneg ((n : ℝ) - 7 : ℝ)]
          nlinarith
        linarith
      linarith
    linarith [h7, h4]