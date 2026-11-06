import Mathlib

theorem algebra_179396 {x y S a b : ℤ} (hS : S = x + y) (hdiv : S ∣ x * a + y * b) :
    S ∣ y * a + x * b := by
  rw [hS] at hdiv ⊢
  have h1 : (x + y) ∣ (y * a + x * b) := by
    have h2 : (x + y) ∣ (x * a + y * b) := hdiv
    -- We need to express y * a + x * b in terms of multiples of (x + y) and (x * a + y * b)
    -- We have the identity: y * a + x * b = (a + b) * (x + y) - (x * a + y * b)
    have h7 : (y * a + x * b) = ((a + b) * (x + y) - (x * a + y * b)) := by
      ring
    have h3 : (x + y) ∣ ((a + b) * (x + y) - (x * a + y * b)) := by
      have h4 : (x + y) ∣ (x * a + y * b) := h2
      have h5 : (x + y) ∣ (a + b) * (x + y) := by
        use a + b
        all_goals ring
      have h6 : (x + y) ∣ ((a + b) * (x + y) - (x * a + y * b)) := by
        apply Dvd.dvd.sub
        · exact h5
        · exact h4
      exact h6
    rw [h7]
    exact h3
  exact h1