import Mathlib

open Real

theorem algebra_232954 {f : ℝ → ℝ} (hf : f = fun x => log ((1 + x) / (1 - x))) (y z : ℝ)
    (hy : -1 < y) (hz : -1 < z) (h1 : f ((y + z) / (1 + y * z)) = 1) (h2 : f ((y - z) / (1 - y * z)) = 2)
    (h3 : y < 1) (h4 : z < 1) :
    f y * f z = -3 / 4 := by
  have f_def : ∀ x, f x = log ((1 + x) / (1 - x)) := by
    intro x
    rw [hf]
  have eq1 : log ((1 + (y + z) / (1 + y * z)) / (1 - (y + z) / (1 + y * z))) = 1 := by 
    rw [f_def] at h1
    simpa using h1
  have eq2 : log ((1 + (y - z) / (1 - y * z)) / (1 - (y - z) / (1 - y * z))) = 2 := by 
    rw [f_def] at h2
    simpa using h2
  have eq3 : (1 + (y + z) / (1 + y * z)) / (1 - (y + z) / (1 + y * z)) = (1 + y) * (1 + z) / ((1 - y) * (1 - z)) := by
    have h5 : 1 + y * z ≠ 0 := by
      nlinarith
    field_simp [h5]
    <;> ring
  have eq4 : (1 + (y - z) / (1 - y * z)) / (1 - (y - z) / (1 - y * z)) = (1 + y) * (1 - z) / ((1 - y) * (1 + z)) := by
    have h6 : 1 - y * z ≠ 0 := by
      nlinarith
    field_simp [h6]
    <;> ring
  rw [eq3] at eq1
  rw [eq4] at eq2

  have eq5a : ( (1 + y) * (1 + z) / ((1 - y) * (1 - z)) ) = ( (1 + y) / (1 - y) ) * ( (1 + z) / (1 - z) ) := by
    have hy1 : 1 - y ≠ 0 := by linarith
    have hz1 : 1 - z ≠ 0 := by linarith
    have hy2 : 1 + y ≠ 0 := by linarith
    have hz2 : 1 + z ≠ 0 := by linarith
    field_simp [hy1, hz1, hy2, hz2]
    <;> ring
    <;> field_simp
    <;> ring
    all_goals nlinarith
  rw [eq5a] at eq1
  have eq6a : log ( ((1 + y) / (1 - y)) * ((1 + z) / (1 - z)) ) = log ( (1 + y) / (1 - y) ) + log ( (1 + z) / (1 - z) ) := by
    have hy1 : 1 - y ≠ 0 := by linarith
    have hz1 : 1 - z ≠ 0 := by linarith
    have hy2 : 1 + y ≠ 0 := by linarith
    have hz2 : 1 + z ≠ 0 := by linarith
    have h1 : ( (1 + y) / (1 - y) ) > 0 := by
      apply div_pos
      all_goals linarith
    have h2 : ( (1 + z) / (1 - z) ) > 0 := by
      apply div_pos
      all_goals linarith
    have h1n : ( (1 + y) / (1 - y) ) ≠ 0 := by positivity
    have h2n : ( (1 + z) / (1 - z) ) ≠ 0 := by positivity
    exact log_mul (by linarith) (by linarith)
  rw [eq6a] at eq1
  
  have eq7a : ((1 + y) * (1 - z) / ((1 - y) * (1 + z)) ) = ( (1 + y) / (1 - y) ) * ( (1 - z) / (1 + z) ) := by
    have hy1 : 1 - y ≠ 0 := by linarith
    have hz1 : 1 + z ≠ 0 := by linarith
    have hy2 : 1 + y ≠ 0 := by linarith
    have hz2 : 1 - z ≠ 0 := by linarith
    field_simp [hy1, hz1, hy2, hz2]
    <;> ring
    <;> field_simp
    <;> ring_nf
    <;> linarith
  rw [eq7a] at eq2
  have eq8a : log ( ((1 + y) / (1 - y) ) * ( (1 - z) / (1 + z) ) ) = log ( (1 + y) / (1 - y) ) + log ( (1 - z) / (1 + z) ) := by
    have hy1 : 1 - y ≠ 0 := by linarith
    have hz1 : 1 + z ≠ 0 := by linarith
    have hy2 : 1 + y ≠ 0 := by linarith
    have hz2 : 1 - z ≠ 0 := by linarith
    have h1 : ( (1 + y) / (1 - y) ) > 0 := by
      apply div_pos
      all_goals linarith
    have h2 : ( (1 - z) / (1 + z) ) > 0 := by
      apply div_pos
      all_goals linarith
    have h1n : ( (1 + y) / (1 - y) ) ≠ 0 := by positivity
    have h2n : ( (1 - z) / (1 + z) ) ≠ 0 := by positivity
    exact log_mul (by linarith) (by linarith)
  rw [eq8a] at eq2
  
  have eq9a : log ( (1 - z) / (1 + z) ) = - log ( (1 + z) / (1 - z) ) := by
    have hy1 : 1 - z ≠ 0 := by linarith
    have hz1 : 1 + z ≠ 0 := by linarith
    have h4 : log ( (1 - z) / (1 + z) ) = log (1 - z) - log (1 + z) := by
      rw [show (1 - z) / (1 + z) = (1 - z) / (1 + z) by rfl]
      rw [log_div (by linarith) (by linarith)]
    have h5 : log ( (1 + z) / (1 - z) ) = log (1 + z) - log (1 - z) := by
      rw [show (1 + z) / (1 - z) = (1 + z) / (1 - z) by rfl]
      rw [log_div (by linarith) (by linarith)]
    rw [h4]
    have h6 : log ( (1 + z) / (1 - z) ) = log (1 + z) - log (1 - z) := h5
    linarith [h6]

  have hA : log ((1 + y) / (1 - y)) = 3 / 2 := by
    linarith [eq1, eq2, eq9a]
  
  have hB : log ((1 + z) / (1 - z)) = -1 / 2 := by
    linarith [eq1, hA, eq9a]
  
  have eq13a : f y = log ((1 + y) / (1 - y)) := by
    rw [f_def]
    <;> simp
    <;> field_simp <;> ring_nf <;> field_simp <;> ring_nf
    all_goals linarith
  have eq14a : f z = log ((1 + z) / (1 - z)) := by
    rw [f_def]
    <;> simp
    <;> field_simp <;> ring_nf <;> field_simp <;> ring_nf
    all_goals linarith
  
  rw [eq13a, eq14a]
  rw [hA, hB]
  all_goals norm_num
  all_goals nlinarith