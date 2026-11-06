import Mathlib

theorem algebra_291760 {x y : ℝ} (hx : (x - 1)^2003 + 2002 * (x - 1) = -1) (hy : (y - 2)^2003 + 2002 * (y - 2) = 1) : x + y = 3 := by 
  let f : ℝ → ℝ := fun x => x ^ 2003 + 2002 * x
  let g : ℝ → ℝ := fun x => x 
  have f_odd : ∀ x, f (-x) = -f x := by
    intro z
    unfold f
    have aux : (-z) ^ 2003 = (-1 ) * z ^ 2003 := by
      ring
    rw [aux]
    ring
  have fmo : StrictMono f := by 
    have mo1 : Monotone (fun (x : ℝ) => x ^ 2003) := by 
      refine monotone_of_deriv_nonneg ?_ ?_
      simp
      intro x
      simp
      positivity
    have mo2 : StrictMono (fun (x : ℝ) => 2002 * x) := by 
      unfold StrictMono
      intro a b hab
      simp
      exact hab
    have feq : f = (fun (x : ℝ) => x ^ 2003) + (fun (x : ℝ) => 2002 * x) := by 
      funext t
      unfold f
      simp
    rw [feq]
    unfold StrictMono
    intro a b hab
    simp
    have aleb : a ≤ b := by
      exact le_of_lt hab
    unfold Monotone at mo1
    obtain ineq_aux := mo1 aleb
    simp at ineq_aux
    unfold StrictMono at mo2
    obtain aux2 := mo2 hab
    simp only at aux2
    exact add_lt_add_of_le_of_lt ineq_aux aux2
  have feq : f (x - 1) = f (2 - y):= by
    have aux : 2 - y = - (y - 2) := by ring
    rw [aux, f_odd (y - 2)]
    unfold f
    rw [hx, hy]
  have eq_aux : x - 1 = 2 - y := by 
    by_cases hx1 : x - 1 < 2 - y
    unfold StrictMono at fmo
    obtain h' := fmo hx1
    rw [feq] at h'
    simp at h'
    by_cases hx2 : x - 1 > 2 - y
    unfold StrictMono at fmo
    obtain h' := fmo hx2
    rw [feq] at h'
    simp at h'
    simp at hx1
    simp at hx2
    apply eq_of_le_of_le
    simp
    exact hx2
    simp
    exact hx1
  calc 
    _ = (x - 1) + 1 + y := by ring
    _ = (2 - y) + 1 + y := by rw [eq_aux]
    _ = 3 := by ring