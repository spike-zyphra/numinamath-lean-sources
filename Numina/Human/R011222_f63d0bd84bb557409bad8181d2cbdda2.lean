import Mathlib.Tactic

/- 23rd APMC 2000 Problem 9 Show that 2 ≤ (1 - x 2 ) 2 + (1 - y 2 ) 2 + (1 - z 2 ) 2 ≤ (1 + x)(1 + y)(1 + z) for non-negative reals x, y, z with sum 1. -/
theorem inequalities_146718 (x y z : ℝ)
    (h₀ : 0 ≤ x) (h₁ : 0 ≤ y) (h₂ : 0 ≤ z)
    (h₃ : x + y + z = 1) :
    2 ≤ (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2 ∧
    (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2 ≤ (1 + x) * (1 + y) * (1 + z) := by
  -- let's define A, B, C, D as some positive expressions we'll analyze
  let q:∃ A:ℝ, A = x^2+y^2+z^2 := by
    simp only [exists_eq]
  obtain ⟨A, Adef⟩ := q
  let q:∃ B:ℝ, B = x*y+y*z+z*x := by
    simp only [exists_eq]
  obtain ⟨B, Bdef⟩ := q
  let q:∃ C:ℝ, C = x^2*y^2+y^2*z^2+z^2*x^2 := by
    simp only [exists_eq]
  obtain ⟨C, Cdef⟩ := q
  let q:∃ D:ℝ, D = x*y*z := by
    simp only [exists_eq]
  obtain ⟨D, Ddef⟩ := q
  -- now we can obtain some results
  have h0:1=A+2*B := by
    rw [Adef, Bdef, show 1=(x+y+z)^2 by rw [h₃]; norm_num]
    ring_nf
  have h1:B^2=C+2*D := by
    rw [Bdef, Cdef, Ddef]; ring_nf
    simp
    rw [← add_mul, ← add_mul, show x * y * z ^ 2 + x * y ^ 2 * z + x ^ 2 * y * z = x*y*z*(x+y+z) by ring_nf, h₃, mul_one]
  have h2:=
    calc x^4+y^4+z^4
    _ = A^2-2*C := by rw [Adef, Cdef]; ring_nf
    _ = 4*B^2-4*B+1-2*C := by rw [show A=1-2*B by linarith]; ring_nf
    _ = 2*C-4*B+8*D+1 := by rw [h1]; ring_nf
  -- now we can estimate the "middle term"
  have h3:=
    calc (1-x^2)^2+(1-y^2)^2+(1-z^2)^2
    _ = 3-2*(x^2+y^2+z^2)+x^4+y^4+z^4 := by ring_nf
    _ = 3-2*A+2*C-4*B+8*D+1:= by rw [Adef, show 3 - 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x ^ 4 + y ^ 4 + z ^ 4 = 3 - 2 * (x ^ 2 + y ^ 2 + z ^ 2) + (x ^ 4 + y ^ 4 + z ^ 4) by ring_nf, h2]; ring_nf
    _ = 2*1+2-2*A+2*C-4*B+8*D := by ring_nf
    _ = 2*(A+2*B)+2-2*A+2*C-4*B+8*D := by rw [h0]
    _ = 2+2*C+8*D := by ring_nf
  rw [h3]
  -- since C and D are positive, we get the first inequality
  constructor
  linarith [show 0≤C by rw [Cdef]; positivity, show 0≤D by rw [Ddef]; positivity]
  -- for the rhs we can also express it with our terms
  rw [show (1 + x) * (1 + y) * (1 + z) = 1+(x+y+z)+B+D by rw [Bdef, Ddef]; ring_nf, h₃]
  norm_num
  suffices 0 ≤ B+D-2*C-8*D by linarith
  rw [show C=B^2-2*D by linarith, show B + D - 2 * (B ^ 2 - 2 * D) - 8 * D = B-2*B^2-3*D by ring_nf];
  -- we show that B≤A by cauchy schwarz
  have h4: B≤A := by
    rw [Bdef, Adef]
    let q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![x, y, z] := by
      simp only [exists_eq]
    obtain ⟨v, vdef⟩ := q
    let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![y, z, x] := by
      simp only [exists_eq]
    obtain ⟨w, wdef⟩ := q
    have h' := real_inner_mul_inner_self_le v w
    simp at h'
    rw [vdef, wdef] at h';
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h';
    simp at h'
    rw [show (x * y + y * z + z * x) * (x * y + y * z + z * x) = (x * y + y * z + z * x)^2 by ring_nf,
        show (x * x + y * y + z * z) * (y * y + z * z + x * x) = (x^2 + y^2 + z^2)^2 by ring_nf] at h'
    apply sq_le_sq.mp at h'
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h'
    exact h'
  -- we can now do another estimate
  have h5:=
    calc B^2
    _ = B*B := by ring_nf
    _ ≤ B*A := by gcongr; rw [Bdef]; positivity
    _ = B*(1-2*B) := by rw [show A=1-2*B by linarith]
    _ = B-2*B^2 := by ring_nf
  -- therefore we can simplify our goal
  suffices 0≤ B^2-3*D by linarith
  -- we can rewrite using other terms
  rw [h1, show C+2*D-3*D=C-D by ring_nf]
  simp
  -- so we only need to show that D≤C, which is another cauchy-schwarz
  rw [Ddef, Cdef]
  let q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![x*y, y*z, z*x] := by
    simp only [exists_eq]
  obtain ⟨v, vdef⟩ := q
  let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![y*z, z*x, x*y] := by
    simp only [exists_eq]
  obtain ⟨w, wdef⟩ := q
  have h' := real_inner_mul_inner_self_le v w
  simp at h'
  rw [vdef, wdef] at h';
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h';
  simp at h'
  rw [show (x * y * (y * z) + y * z * (z * x) + z * x * (x * y)) * (x * y * (y * z) + y * z * (z * x) + z * x * (x * y)) = (x * y * (y * z) + y * z * (z * x) + z * x * (x * y))^2 by ring_nf,
      show y * z * (y * z) + z * x * (z * x) + x * y * (x * y) = (x * y * (x * y) + y * z * (y * z) + z * x * (z * x)) by ring_nf,
      show (x * y * (x * y) + y * z * (y * z) + z * x * (z * x)) * (x * y * (x * y) + y * z * (y * z) + z * x * (z * x)) = (x * y * (x * y) + y * z * (y * z) + z * x * (z * x))^2 by ring_nf,
      show x * y * (x * y) + y * z * (y * z) + z * x * (z * x) = x^2*y^2+y^2*z^2+z^2*x^2 by ring_nf,
      show x * y * (y * z) + y * z * (z * x) + z * x * (x * y) = x*y*z*(x+y+z) by ring_nf,
      h₃, mul_one
  ] at h'
  apply sq_le_sq.mp at h'
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h'
  exact h'