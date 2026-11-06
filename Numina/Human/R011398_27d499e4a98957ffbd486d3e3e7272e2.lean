import Mathlib

open Algebra
open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- 23. (HUN 4) Prove that for an arbitrary pair of vectors $f$ and $g$ in the plane, the inequality  $$ a f^{2}+b f g+c g^{2} \geq 0 $$  holds if and only if the following conditions are fulfilled: $a \geq 0, c \geq 0$, $4 a c \geq b^{2}$. -/
theorem inequalities_24643 (a b c : ℝ) :
(∀ f g : EuclideanSpace ℝ (Fin 2), a * inner f f + b * inner f g + c * inner g g ≥ 0)
↔ 
(a ≥ 0 ∧ c ≥ 0 ∧ 4 * a * c ≥ b ^ 2) := by

  constructor

  --From left to right.
  intro h
  simp at h
  simp

  --We use the vector (t,0) and (1,0) as special cases.
  have cla : ∀ t:ℝ, 0 ≤ a * (t*t) + b * t + c := by 
    intro t
    let g : EuclideanSpace ℝ (Fin 2)  :=  fun x => match x with 
      | 0 => 1
      | 1 => 0
    let f : EuclideanSpace ℝ (Fin 2)  :=  fun x => match x with 
      | 0 => t
      | 1 => 0

    specialize h f g
    simp [f,g] at h
    exact h
  -- Now at^2+bt+c is always nonnegtaive. This implies that a>0,c>0,b^2-4ac≤0.
  have cnn : 0 ≤ c := by 
    specialize cla 0
    simp at cla
    exact cla
  have dis : discrim a b c ≤ 0 := by 
    apply discrim_le_zero
    exact cla
  unfold discrim at dis
  
  constructor
  by_contra aneg
  push_neg at aneg
  by_cases cpos : 0 < c
  nlinarith
  have ce0 : c = 0 := by linarith
  simp [ce0] at dis
  have be0 : b = 0 := by nlinarith
  specialize cla 1
  simp [be0,ce0] at cla
  linarith

  constructor
  exact cnn
  linarith


  --From right to left.
  intro h
  simp at h
  obtain ⟨ann,cnn,hdis⟩ := h
  
  intro f g
  simp

  by_cases ae0 : a = 0 
  simp [ae0] at hdis ⊢
  have be0 : b = 0 := by nlinarith
  simp [be0]
  nlinarith

  --We rewrite the given equation to the following form.
  have eq : a * (f 0 * f 0 + f 1 * f 1) + b * (f 0 * g 0 + f 1 * g 1) + c * (g 0 * g 0 + g 1 * g 1) = a * ((f 0 + b / (2*a) * g 0) * (f 0 + b / (2*a) * g 0) + (f 1 + b / (2*a) * g 1)*(f 1 + b / (2*a) * g 1)) + ((4*a*c - b^2)/(4*a)) * (g 0 * g 0 + g 1 * g 1) := by
    field_simp
    ring_nf
  rw [eq]
  --Now, these two terms are non-negavite. Hence, their sum is also non-negative.
  have : 0 ≤ a * ((f 0 + b / (2 * a) * g 0) * (f 0 + b / (2 * a) * g 0) + (f 1 + b / (2 * a) * g 1) * (f 1 + b / (2 * a) * g 1))  := by 
    nlinarith
  have : 0 ≤ (4 * a * c - b ^ 2) / (4 * a) * (g 0 * g 0 + g 1 * g 1) := by 
    have t1 : 0 ≤ (4 * a * c - b ^ 2) / (4 * a) := by 
      refine div_nonneg ?_ ?_
      linarith
      linarith
    have t2 : 0 ≤ (g 0 * g 0 + g 1 * g 1) := by nlinarith
    exact Left.mul_nonneg t1 t2
  linarith