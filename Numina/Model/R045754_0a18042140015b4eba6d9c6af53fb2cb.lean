import Mathlib

theorem algebra_207710 {f : ℤ → ℤ} (hf : ∃ a b, f = fun x => a * x + b)
    (h0 : f (f 0) = 0) (h4 : f (f (f 4)) = 9) :
    ∑ i ∈ Finset.range 2015, f (f (f (f i))) = 2029105 := by
  rcases hf with ⟨a, b, hf_eq⟩
  have eq1 : f (f 0) = a * b + b := by
    rw [hf_eq]
    <;> simp [hf_eq]
  have eq1' : a * b + b = 0 := by 
    linarith [h0, eq1]
  have eq2 : b * (a + 1) = 0 := by
    linarith
  have eq3 : f (f (f 4)) = 4 * a ^ 3 + a ^ 2 * b + a * b + b := by
    rw [hf_eq]
    <;> simp [hf_eq]
    <;> ring
  have eq3' : 4 * a ^ 3 + a ^ 2 * b + a * b + b = 9 := by
    linarith [h4, eq3]
  have h1 : b = 0 ∨ a = -1 := by 
    cases (mul_eq_zero.mp eq2) with
    | inl h => 
      left; linarith
    | inr h => 
      right; linarith
  cases h1 with
  | inl hb0 =>
    have eq4 : 4 * a ^ 3 = 9 := by
      rw [hb0] at eq3'
      linarith
    exfalso
    have h5 : a ≤ 1 := by
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have h6 : a ≥ 1 := by 
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a - 1), sq_nonneg (a + 1)]
    interval_cases a <;> omega
  | inr ha_m1 =>
    have eq4 : b = 13 := by
      rw [show a = -1 by linarith] at eq3'
      nlinarith
    have h5 : ∀ x, f (f (f (f x))) = x := by
      intro x 
      simp [hf_eq, eq4, ha_m1]
      <;> ring
    have h6 : ∑ i in Finset.range 2015, f (f (f (f i))) = ∑ i in Finset.range 2015, (i : ℤ) := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi 
        rw [h5 i] 
    rw [h6]
    native_decide