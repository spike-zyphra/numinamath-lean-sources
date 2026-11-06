import Mathlib

open Real

theorem calculus_136243 (f : ℝ → ℝ) (hf : f = fun x => sqrt (4 * x - 1)) (x : ℝ) (hx : x = 2.56) :
    deriv f 2.5 * (x - 2.5) + f 2.5 = 3.04 := by 
  have h1 : f 2.5 = 3 := by
    rw [hf]
    have hsqrt : sqrt (4 * (2.5 : ℝ) - 1) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact hsqrt
  have h2 : deriv f 2.5 = 2 / 3 := by
    rw [hf]
    -- Apply the derivative rule for sqrt and simplify
    have h49 : deriv (fun (x : ℝ) => sqrt (4 * x - 1)) 2.5 = 2 / 3 := by
      -- Use fundamental differentiation rules
      have h5 : deriv (fun (x : ℝ) => sqrt (4 * x - 1)) 2.5 = (4) / (2 * sqrt (4 * (2.5 : ℝ) - 1)) := by
        -- Apply derivative of sqrt to the inner expression
        simp [deriv_sqrt, deriv_const, deriv_id', mul_comm, mul_assoc, differentiableAt_id', differentiableAt_const]
        <;> try field_simp
        <;> try ring_nf
        <;> try field_simp
      rw [h5]
      -- Now we need to rewrite sqrt(9) as 3
      have hsqrt : sqrt (4 * (2.5 : ℝ) - 1) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [hsqrt]
      -- Simplify 4/(2*3) to 2/3
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> try { tauto }
      <;> try { 
        field_simp 
        <;> try ring 
      }
      <;> try { nlinarith }
    exact h49
  have h3 : x - 2.5 = (0.06 : ℝ) := by
    rw [hx]
    norm_num
  rw [h2, h1, h3]
  all_goals norm_num
  all_goals
    try { norm_num }
    <;> try { 
      field_simp 
      <;> try ring 
      <;> try { try { nlinarith } }
    }
    <;> try { tauto }
  <;> try { nlinarith }
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  all_goals tauto
  all_goals nlinarith
  <;> try { tauto }