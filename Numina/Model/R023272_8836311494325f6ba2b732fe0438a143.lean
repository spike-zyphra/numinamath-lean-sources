import Mathlib

theorem inequalities_596883 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : d = max (max a b) (max c d)) :
    a * (d - b) + b * (d - c) + c * (d - a) < d ^ 2 := by
  have h1 : d ≥ a := by
    have h2 : d = max (max a b) (max c d) := h
    have h3 : max (max a b) (max c d) ≥ a := by 
      have h4 : max (max a b) (max c d) ≥ max a b := by 
        cases max_cases (max a b) (max c d) with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      have h5 : max a b ≥ a := by 
        cases max_cases a b with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      linarith
    linarith [h2, h3]
  have h2 : d ≥ b := by
    have h2 : d = max (max a b) (max c d) := h
    have h3 : max (max a b) (max c d) ≥ b := by
      have h4 : max (max a b) (max c d) ≥ max a b := by 
        cases max_cases (max a b) (max c d) with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      have h5 : max a b ≥ b := by 
        cases max_cases a b with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      linarith
    linarith [h2, h3]
  have h3 : d ≥ c := by
    have h2 : d = max (max a b) (max c d) := h
    have h4 : max (max a b) (max c d) ≥ c := by
      have h5 : max (max a b) (max c d) ≥ max c d := by 
        cases max_cases (max a b) (max c d) with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      have h6 : max c d ≥ c := by 
        cases max_cases c d with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      linarith
    linarith [h2, h4]
  nlinarith [sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (d - c), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos ha hd, mul_pos hb hd, mul_pos hc hd, 
          mul_nonneg (show 0 ≤ d - a by linarith) (show 0 ≤ d - b by linarith), 
          mul_nonneg (show 0 ≤ d - a by linarith) (show 0 ≤ d - c by linarith), 
          mul_nonneg (show 0 ≤ d - b by linarith) (show 0 ≤ d - c by linarith)
]