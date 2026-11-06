import Mathlib

theorem algebra_311878 {x : ℝ} (A B : Finset ℝ)
    (hA : A = {x^2, x + 1, -3}) (hB : B = {x - 5, 2 * x - 1, x^2 + 1})
    (hAB : A ∩ B = {-3}) :
    x = -1 := by
  have h1 : -3 ∈ A ∩ B := by
    rw [hAB]
    simp
  rw [Finset.mem_inter] at h1
  have h2 : -3 ∈ B := h1.2
  rw [hB] at h2
  simp at h2
  cases h2 with
  | inl h_eq1 =>
    have hx : x = 2 := by linarith
    rw [hA, hB, hx] at hAB
    norm_num [Finset.ext_iff] at hAB
    <;> try { norm_num at hAB }
    <;> try { nlinarith }
  | inr h_eq2 =>
    cases h_eq2 with
    | inl h_eq2 =>
      have hx : x = -1 := by linarith
      exact hx
    | inr h_eq3 =>
      nlinarith