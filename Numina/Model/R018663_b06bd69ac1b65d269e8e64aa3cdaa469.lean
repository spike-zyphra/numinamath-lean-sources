import Mathlib

open Real

theorem calculus_143182 (f : ℝ → ℝ) (hf : f = fun x => x / (x ^ 2 + 1)) (x0 : ℝ) (hx0 : x0 = -2) :
    ∃ m c, f x0 = m * x0 + c ∧ m = deriv f x0 ∧ c = f x0 - m * x0 := by
  use (-3 / 25)
  use (-16 / 25)
  rw [hx0]
  constructor
  · -- Show that f(-2) = (-3/25) * (-2) + (-16/25)
    rw [hf]
    norm_num
    <;> field_simp
    <;> norm_num
  constructor
  · -- Show that -3/25 = deriv f (-2)
    rw [hf]
    have h1 : deriv (fun (x : ℝ) => x / (x ^ 2 + 1)) (-2 : ℝ) = -3 / 25 := by
      have h2 : deriv (fun (x : ℝ) => x / (x ^ 2 + 1)) (-2 : ℝ) = (1 * ((-2) ^ 2 + 1) - (-2) * (2 * (-2))) / ((-2) ^ 2 + 1) ^ 2 := by
        simp [deriv_div, deriv_id'', deriv_pow, mul_comm, mul_assoc]
        all_goals
        try { norm_num }
        <;> try { field_simp }
        <;> try { norm_num }
        <;> try { ring_nf }
        <;> try { norm_num }
        <;> try { native_decide }
        <;> try { ring_nf }
      rw [h2]
      norm_num
      <;> field_simp
      <;> norm_num
    rw [h1]
    all_goals norm_num
  · -- Show that -16/25 = f(-2) - (-3/25) * (-2)
    rw [hf]
    norm_num
    <;> field_simp
    <;> norm_num
    <;> ring_nf
    <;> field_simp
    <;> norm_num