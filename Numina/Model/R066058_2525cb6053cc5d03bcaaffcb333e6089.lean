import Mathlib

theorem algebra_109218 (r : Fin 50 → ℝ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) (hriq' : ∀ i, ¬Irrational (ir i))
    (hriq'' : {i | Irrational (ir i)}.encard = 50)
    (hriq''' : {i | ¬Irrational (ir i)}.encard = 50) :
    {i | ∃ j, ¬Irrational (r i + ir j)}.encard ≤ 1250 := by
  have h1 := hriq 0
  have h2 := hriq' 0
  contradiction