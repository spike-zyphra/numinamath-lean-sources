import Mathlib
open Real
open Complex

/-
Find all the roots of the polynomial $x^{5}-5 x^{4}+11 x^{3}-13 x^{2}+9 x-3$.
-/
theorem algebra_609462 (x:ℂ) (h: x^5 - 5*x^4 + 11*x^3 - 13*x^2 + 9*x -3 = 0): ((x = 1) ∨ (x = (3 + sqrt 3 * I)/2) ∨ (x = (1 - sqrt 3 * I)/2) ∨ (x = (3 - sqrt 3 * I)/2) ∨ (x = (1 + sqrt 3 * I)/2)) := by
  let z:ℂ := x-1

  -- some useful lemmas with x-a=0 then x = a as complex numbers
  have lemma_min (x a:ℂ) (h: x-a = 0) : x = a := by rw [sub_eq_zero] at h; exact h

  -- take z = x-1, then x = z+1, rw this to the equation
  have h': x^5 - 5*x^4 + 11*x^3 - 13*x^2 + 9*x -3 = z*(z^4 + z^2 + 1) := by
    unfold z; ring_nf
  -- it is sufficient to find roots for z^4+z^2+1=0.
  rw [h'] at h

  -- take z^2 as a new variable, then factorize the equation
  have hn_zn: z^4 + z^2 + 1 = (z^2 - ((-1 + sqrt 3 * I)/2))*(z^2 - ((-1 - sqrt 3 * I)/2)) := by
    ring_nf
    have : I^2 = -1  := I_sq
    rw [this]
    field_simp
    norm_cast
    have : (sqrt 3)^2 = 3 := by norm_num
    rw [this]
    norm_cast
    ring_nf

  -- it is sufficient to find roots for z^2 - ((-1 + sqrt 3 * I)/2) = 0 and z^2 - ((-1 - sqrt 3 * I)/2) = 0
  have hn_z1: z^2 - ((-1 + sqrt 3 * I)/2) = (z - ((1 + sqrt 3 * I)/2)) * (z + ((1 + sqrt 3 * I)/2)) := by
    ring_nf
    have : ((sqrt 3):ℂ) ^ 2 = 3 := by
      norm_cast; norm_num
    rw [this]
    ring_nf
    have : I^2 = -1  := I_sq
    rw [this]
    ring_nf
  have hn_z2: z^2 - ((-1 - sqrt 3 * I)/2) = (z - ((-1 + sqrt 3 * I)/2)) * (z + ((-1 + sqrt 3 * I)/2)) := by
    ring_nf
    have : ((sqrt 3):ℂ) ^ 2 = 3 := by
      norm_cast; norm_num
    rw [this]
    ring_nf
    have : I^2 = -1  := I_sq
    rw [this]
    ring_nf
  rw [hn_z1, hn_z2] at hn_zn
  rw [hn_zn] at h
  unfold z at h

  -- it is sufficient to find all roots for the formal equation
  have hend: (x-1)*(x - ((3 + sqrt 3 * I)/2))* (x - ((1 - sqrt 3 * I)/2)) * (x - ((3 - sqrt 3 * I)/2))* (x - ((1 + sqrt 3 * I)/2)) = 0 := by
    rw [h.symm]
    ring_nf
  simp at hend

  -- Cases the or operator
  rcases hend with _1 | h2
  rcases _1 with _2 | h3
  rcases _2 with _3 | h4
  rcases _3 with h1 | h5

  have : x= (1:ℂ) := by
    apply lemma_min
    exact h1
  tauto

  have : x= (3 + sqrt 3 * I)/2 := by
    apply lemma_min
    exact h5
  tauto

  have : x= (1 - sqrt 3 * I)/2 := by
    apply lemma_min
    exact h4
  tauto

  have : x= (3 - sqrt 3 * I)/2 := by
    apply lemma_min
    exact h3
  tauto

  have : x= (1 + sqrt 3 * I)/2 := by
    apply lemma_min
    exact h2
  tauto
