import Mathlib
open Complex

/- There is a complex number z with imaginary part 164 and a positive integer n such that z/(z+n)=4i. Find n. -/
theorem algebra_94131 {z : ℂ} (hz : z.im = 164) (n : ℕ) (hn : n > 0)
(h : z / (z + n) = 4 * I) : n = 697 := by
  -- let z = a + 164i
  let q: (∃ a:ℝ, z = a + 164 * I) := by
    use z.re
    apply ext
    · simp
    · simpa
  obtain ⟨a, z_defa⟩ := q
  -- substitute into h
  rw [z_defa] at h
  -- multiply both sides by denominator
  apply congr_arg (fun x => x * (a + 164 * I + n)) at h
  rw [div_mul_cancel₀ _ (by intro hn; apply congr_arg (fun x=> x.im) at hn; simp at hn)] at h
  ring_nf at h;simp at h
  -- split into real and imaginary parts
  have hre:= congr_arg Complex.re h
  have him:= congr_arg Complex.im h
  -- solve the system for n
  simp at hre him
  rw [hre] at him
  ring_nf at him
  apply congr_arg (fun x => (2624+x)/4) at him
  norm_num at him
  norm_cast at him
  exact him.symm