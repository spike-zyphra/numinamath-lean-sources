import Mathlib

open Real

theorem algebra_318986 {f : ℝ → ℝ} (hf : f = fun x => tan (π / 4 - arctan x)) :
    f ((1 - 3 ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + 3 ^ ((1 : ℝ) / 3) + sqrt 2)) = 3 ^ ((1 : ℝ) / 3) + sqrt 2 := by
  have h1 : ∀ x : ℝ, f x = (1 - x) / (1 + x) := by
    intro x
    rw [hf]
    have htan : tan (π / 4 - arctan x) = (1 - x) / (1 + x) := by
      have htan1 : tan (π / 4 - arctan x) = sin (π / 4 - arctan x) / cos (π / 4 - arctan x) := by
        rw [tan_eq_sin_div_cos]
      rw [htan1]
      have h2 : sin (π / 4 - arctan x) = sin (π / 4) * cos (arctan x) - cos (π / 4) * sin (arctan x) := by 
        rw [sin_sub]
      have h3 : cos (π / 4 - arctan x) = cos (π / 4) * cos (arctan x) + sin (π / 4) * sin (arctan x) := by 
        rw [cos_sub]
      rw [h2, h3]
      have h4 : sin (π / 4) = (1 / Real.sqrt 2 : ℝ) := by
        rw [sin_pi_div_four]
        all_goals field_simp
      have h5 : cos (π / 4) = (1 / Real.sqrt 2 : ℝ) := by
        rw [cos_pi_div_four]
        all_goals field_simp
      have htan_y1 : sin (arctan x) = (x / Real.sqrt (1 + x ^ 2) : ℝ) := by
        rw [sin_arctan]
        <;> field_simp
        <;> ring
      have htan_y2 : cos (arctan x) = (1 / Real.sqrt (1 + x ^ 2) : ℝ) := by
        rw [cos_arctan]
        <;> field_simp
        <;> ring
      rw [h4, h5, htan_y1, htan_y2]
      <;> field_simp
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> ring
      <;> norm_num
      <;> field_simp
      all_goals norm_num
    simpa using htan
  have h6 : f ((1 - 3 ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + 3 ^ ((1 : ℝ) / 3) + sqrt 2)) = (1 - ((1 - 3 ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + 3 ^ ((1 : ℝ) / 3) + sqrt 2)) ) / (1 + ((1 - 3 ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + 3 ^ ((1 : ℝ) / 3) + sqrt 2)) ) := by
    apply h1
  rw [h6]
  have h7 : (1 - ((1 - (3 : ℝ) ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + (3 : ℝ) ^ ((1 : ℝ) / 3) + sqrt 2))) = (2 * ((3 : ℝ) ^ ((1 : ℝ) / 3) + sqrt 2)) / (1 + (3 : ℝ) ^ ((1 : ℝ) / 3) + sqrt 2) := by
    field_simp
    <;> 
      ring_nf <;> norm_num <;> ring_nf <;> norm_num
  have h8 : (1 + ((1 - (3 : ℝ) ^ ((1 : ℝ) / 3) - sqrt 2) / (1 + (3 : ℝ) ^ ((1 : ℝ) / 3) + sqrt 2))) = (2) / (1 + (3 : ℝ) ^ ((1 : ℝ) / 3) + sqrt 2) := by
    field_simp
    <;> ring_nf <;> norm_num <;> ring_nf <;> norm_num
  field_simp [h7, h8]
  <;> ring_nf <;> norm_num
  all_goals ring_nf
  all_goals norm_num
  <;> field_simp <;> tauto
  <;> norm_num
  <;> linarith
  <;> norm_num
  <;> field_simp <;> ring
  <;> norm_num <;> nlinarith
  <;> norm_num
  <;> norm_num
  all_goals ring
  all_goals norm_num