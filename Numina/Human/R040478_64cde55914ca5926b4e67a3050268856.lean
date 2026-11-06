import Mathlib

/- 3. Solve the system of equations $\left\{\begin{array}{l}x+\sqrt{x+2 y}-2 y=\frac{7}{2}, \\ x^{2}+x+2 y-4 y^{2}=\frac{27}{2}\end{array}\right.$. -/
theorem algebra_159395 {x y : ℝ} (hx : x ≥ -2 * y) (hy : y ≥ 0)
    (h1 : x + Real.sqrt (x + 2 * y) - 2 * y = 7 / 2) (h2 : x ^ 2 + x + 2 * y - 4 * y ^ 2 = 27 / 2) :
    x = 19 / 4 ∧ y = 17 / 8 := by
  -- let u = √(x+2y); v = x-2y
  let q:∃ u:ℝ, u = √(x+2*y) := by
    use √(x + 2 * y)
  obtain ⟨u, udef⟩ := q
  let q:∃ v:ℝ, v = x - 2 * y := by
    use x - 2 * y
  obtain ⟨v, vdef⟩ := q
  -- plug into original equations
  rw [← udef, add_comm, add_sub_assoc, ← vdef] at h1
  have h2':u^2*v+u^2=27/2:= by
    rw [udef, vdef, Real.sq_sqrt (by linarith)]
    ring_nf at h2 ⊢
    assumption
  -- we can now solve the system of equations
  have h3:v = 7/2 - u := by linarith
  rw [h3] at h2'
  field_simp at h2'; ring_nf at h2'
  apply congr_arg (fun x => x-27) at h2'
  simp at h2'
  -- we can guess u=3 and factor
  conv_lhs at h2' =>
    calc _
    _ = (3 - u) * (u-3)* (u+3/2)*2 := by ring_nf
  simp at h2'
  -- now for the case analysis
  cases' h2' with h2' h2'
  cases' h2' with h2' h2'
  · have h2'' : u = 3 := by
      linarith
    rw [h2''] at h3 udef; norm_num at h3
    rw [h3] at vdef
    apply congr_arg (fun x => x^2) at udef
    rw [Real.sq_sqrt (by linarith)] at udef; norm_num at udef
    exact ⟨by linarith, by linarith⟩
  · have h2'' : u = 3 := by
      linarith
    rw [h2''] at h3 udef; norm_num at h3
    rw [h3] at vdef
    apply congr_arg (fun x => x^2) at udef
    rw [Real.sq_sqrt (by linarith)] at udef; norm_num at udef
    exact ⟨by linarith, by linarith⟩
  · have h2'' : u = -3/2 := by linarith
    rw [h2''] at h3 udef; norm_num at h3
    rw [h3] at vdef
    apply congr_arg (fun x => x^2) at udef
    rw [Real.sq_sqrt (by linarith)] at udef; norm_num at udef
    exact ⟨by linarith, by linarith⟩