import Mathlib

theorem algebra_14289 {d e : ℝ} (hd : d^2 + (3 / 2) * d - (5 / 2) = 0) (he : e^2 + (3 / 2) * e - (5 / 2) = 0)
    (hde : d ≠ e) : (d - 1) * (e - 1) = 0 := by

  have h1 : (d - 1) * (2 * d + 5) = 0 := by
    have h2 : 2 * d^2 + 3 * d - 5 = 0 := by 
      linarith [hd]
    have h3 : (d - 1) * (2 * d + 5) = 0 := by
      linarith [h2]
    exact h3
  have h2 : (e - 1) * (2 * e + 5) = 0 := by
    have h4 : 2 * e^2 + 3 * e - 5 = 0 := by
      linarith [he]
    have h5 : (e - 1) * (2 * e + 5) = 0 := by
      linarith [h4]
    exact h5
  
  cases' (mul_eq_zero.mp h1) with h1 h1

  · -- Case where $d - 1 = 0$, so $d = 1$, and thus $(d - 1) * (e - 1) = 0$
    have : (d - 1) * (e - 1) = 0 := by
      rw [show d - 1 = 0 by linarith]
      ring
    linarith
  
  · -- Case where $2d + 5 = 0$, so $d = -5/2$
    have h5 : d = -5 / 2 := by linarith

    cases' (mul_eq_zero.mp h2) with h6 h7

    · -- Case where $e - 1 = 0$, so $e = 1$, and thus $(d - 1) * (e - 1) = 0$
      have : (d - 1) * (e - 1) = 0 := by
        rw [show e - 1 = 0 by linarith]
        ring
      linarith

    · -- Case where $2e + 5 = 0$, so $e = -5/2$
      have h8 : e = -5 / 2 := by linarith

      -- Now if $d = -5/2$ and $e = -5/2$ then $d = e$, contradicting $d ≠ e$
      have h_eq : d = e := by
        linarith [h5, h8]

      -- Derive contradiction from the equality $d = e$ and the hypothesis $d ≠ e$
      contradiction