import Mathlib

theorem Inequalities_613610
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 1 / 3 ≥
    8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) := by 
  let x := a + b + c
  let y := a * b + b * c + c * a
  let z := a * b * c
  have neq : (9 * ((a + b + c) * (a * b + b * c + c * a) - a * b * c)) ≠ 0 := by 
    have aux : (9 * ((a + b + c) * (a * b + b * c + c * a) - a * b * c)) > 0 := by 
      ring_nf
      positivity
    exact Ne.symm (ne_of_lt aux)
  have h1 : (a ^ 2 + b ^ 2 + c ^ 2 + 3 * (a * b + b * c + c * a)) / (a * b + b * c + c * a) = (x ^ 2 + y) / y := by 
    unfold x
    unfold y
    ring
  -- use ring to prove the following equality
  have h2 :  8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b))
    + (8 / (3 : ℝ)) = 
    8 / 9 * (x ^ 3 + x * y) / (x * y - z) := by 
    unfold x 
    unfold y
    unfold z
    field_simp
    ring_nf
  -- use the geom_le_mean inequalities or use the following argument. 
  have ineq_aux : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≥ 6 * a * b * c := by 
    have h1 : c *(a - b) ^ 2 + a * (b - c) ^ 2 + b *(c - a) ^ 2 ≥ 0 := by nlinarith
    nlinarith
  have ineq0 : x * y ≥ 9 * z := by 
    unfold x 
    unfold y
    unfold z 
    ring_nf
    nlinarith
  have ineq3 : 8 * (x ^ 3 + x * y) * y ≤ (x ^ 2 + y) * (9 * (x * y - z)) := by 
    have aux : 8 * x * y ≤ 9 * x * y - 9 * z := by 
      linarith
    obtain h' := mul_le_mul_of_nonneg_left aux (by positivity) (a := x ^ 2 + y)
    nlinarith
  have aux : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 3 ≥
    8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) + 8/(3 : ℝ) := by 
    calc  
      _ = (x ^ 2 + y) / y := by 
        rw [←h1]
        field_simp
      _ ≥ 8 / 9 * (x ^ 3 + x * y) / (x * y - z) := by 
        field_simp
        refine (div_le_div_iff₀ ?_ ?_).mpr ?_
        unfold x 
        unfold y
        unfold z
        ring_nf
        positivity
        unfold y
        nlinarith
        nlinarith
      _ = _ := by
        rw [h2]
  linarith