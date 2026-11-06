import Mathlib

theorem algebra_10640 {f : ℝ → ℝ} (hf : f = fun x => (x - 5) * (x ^ 2 + 5 * x + 6)) :
    Set.ncard {x | f x = 0} = 3 := by
  have h1 : {x | f x = 0} = {5, -2, -3} := by
    ext x
    simp [hf]
    constructor
    · -- Show that if $f(x) = 0$, then $x ∈ \{-3, -2, 5\}$.
      intro h
      have h2 : (x - 5) * (x ^ 2 + 5 * x + 6) = 0 := by
        simpa using h
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- If $x - 5 = 0$, then $x = 5$, so x ∈ {5, -2, -3}
        have hx : x = 5 := by linarith
        simp [hx]
      · -- If x^2 + 5 x + 6 = 0, then x = -2 or x = -3
        have h5 : x^2 + 5 * x + 6 = 0 := by
          linarith
        have h6 : (x + 2) * (x + 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- Case $x + 2 = 0$, so x = -2
          have hx : x = -2 := by linarith
          simp [hx]
        · -- Case $x + 3 = 0$, so x = -3
          have hx : x = -3 := by linarith
          simp [hx]
    · -- Show that if $x ∈ \{-3, -2, 5\}$, then $f(x) = 0$.
      rintro (rfl | rfl | rfl)
      · -- x = 5
        norm_num
      · -- x = -2
        norm_num
      · -- x = -3
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  norm_num