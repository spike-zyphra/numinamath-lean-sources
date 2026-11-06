import Mathlib

/-Find the minimum value of  (9 * x^2*(sin x)^2+4)/(x*sin x)for 0< x <π.-/

open Real Set

theorem AIME_Algebra_94506 :
IsLeast {y : ℝ | ∃ x : ℝ, x ∈ Ioo 0 Real.pi ∧ y = (9 * x ^ 2 * sin x ^ 2 + 4) / (x * sin x)} 12 := by
--We need to prove two facts, the first is that every member of this set is no less than 12, the second is that 12 is contained in this set.
  set f:Real->Real:=(fun x=>x*sin x) with fdef
  simp only [IsLeast]
  simp only [lowerBounds]
  simp only [mem_Ioo, mem_setOf_eq, forall_exists_index, and_imp]
  constructor
  swap
--We rewrite the inequality as 12≤(9* (f x)^2+4)/(f x)
  intro a x xpos xltpi ha
  rw[ha]
  suffices 12≤ (9* (f x)^2+4)/(f x) by
    simp only [f] at this
    ring_nf at this
    ring_nf
    exact this
--We prove that this inequality holds for general real numbers not only those of the form f x.
  suffices h: ∀(x:Real),12*x≤(9*x^2+4) by
    rw[le_div_iff]
    apply h
    simp only [f]
    apply mul_pos xpos
    apply sin_pos_of_mem_Ioo
    constructor
    exact xpos
    exact xltpi
  intro x
--This is because square of real numbers are nonnegative.
  suffices 0≤(3*x-2)^2 by
    ring_nf at this
    linarith
  apply sq_nonneg
--Now we prove that 12 lies in this set, it suffices to show that there exists x s.t. x*sin x=2/3.
  suffices ∃ x∈Ioo 0 Real.pi, x*sin x=2/3 by
    rcases this with ⟨x,⟨xpos,xltpi⟩,hx⟩
    use x
    split_ands
    linarith;linarith
    rw[mul_assoc,←mul_pow,hx]
    norm_num
--It suffices to prove 2/3 lies in the image of f.
  suffices ∃ x∈Ioo 0 Real.pi, f x=2/3 by
    simp only [f] at this
    exact this
  suffices h:Set.Ioo 0 (Real.pi/2) ⊆ f '' Set.Ioo 0 Real.pi by
    simp only [image,Set.subset_def] at h
    simp only [mem_Ioc, mem_Ioo, mem_setOf_eq, and_imp] at h
    apply h
    linarith
    rw[div_lt_div_iff]
    rw[←div_lt_iff]
    norm_num
    apply lt_of_le_of_lt' Real.two_le_pi
    norm_num;norm_num;norm_num;norm_num
  have pidiv2nonneg:0≤Real.pi/2:=by
    rw[div_nonneg_iff]
    left
    constructor
    apply Real.pi_nonneg
    norm_num
  have fzeropi:0=f 0 ∧ Real.pi/2=f (π/2):=by
    simp only [f]
    simp only [sin_zero, mul_zero, sin_pi_div_two, mul_one, and_self]
  nth_rewrite 1[fzeropi.1,fzeropi.2]
--We prove this by using the intermediate value theorem, first, we prove that it is continuous.
  have hf : ContinuousOn f (Icc 0 (Real.pi/2)):=by
    rw[fdef]
--This is because it is the product of two continuous function.
    apply ContinuousOn.mul
    apply continuousOn_id
    apply continuousOn_sin
  apply subset_trans (intermediate_value_Ioo pidiv2nonneg hf)
  apply Set.image_subset
  rw[Set.subset_def]
  intro x ⟨xpos,xa⟩
  constructor
  linarith;linarith