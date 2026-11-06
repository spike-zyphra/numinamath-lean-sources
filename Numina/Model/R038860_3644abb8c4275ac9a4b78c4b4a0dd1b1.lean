import Mathlib

theorem algebra_3594
  (A : ℝ)
  (h : ¬∃ x y z, 2 * x + y + 3 * z = 20 ∧ 3 * x - y + z = 17 ∧ 4 * x - 3 * y + A * z = 326) :
  A = -1 := by 
  by_contra h1 
  push_neg at h1 
  have h2 : A ≠ -1 := by 
    intro h_eq 
    apply h1 
    linarith 
  have h3 : A + 1 ≠ 0 := by 
    intro h_eq 
    have : A = -1 := by linarith 
    contradiction 
  have h4 : ∃ x y z, 2 * x + y + 3 * z = 20 ∧ 3 * x - y + z = 17 ∧ 4 * x - 3 * y + A * z = 326 := by 
    use (37 - 4 * (312 / (A + 1))) / 5, (26 - 7 * (312 / (A + 1))) / 5, 312 / (A + 1)
    constructor 
    · -- First equation 
      field_simp [(show A + 1 ≠ 0 by intro h_eq; apply h3; linarith)]
      <;> ring 
    constructor 
    · -- Second equation 
      field_simp [(show A + 1 ≠ 0 by intro h_eq; apply h3; linarith)]
      <;> ring 
    · -- Third equation 
      field_simp [(show A + 1 ≠ 0 by intro h_eq; apply h3; linarith)]
      <;> ring 
  exfalso 
  apply h 
  exact h4