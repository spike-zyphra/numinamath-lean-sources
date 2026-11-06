import Mathlib

open Real
open Set
open Polynomial

/-- An auxiliary Lemma that the derivative of function $f = ax^2 + bx + c$ equal $2ax + b$-/
lemma l_deriv (a b c : ℝ) : deriv (fun x => a * x ^ 2 + b * x + c) = fun x => 2 * a * x + b := by
  set f := fun x => a * x ^ 2 + b * x + c
  let pf : ℝ[X] := C a * X ^ 2 + C b * X + C c
  rw [show f = fun x => pf.eval x by ext x; simp [f, pf]]
  ext x
  rw [Polynomial.deriv]
  simp [pf]
  ring

def constraint (x y : ℝ) := √ (x - 2) + √ (y - 3) = 3

def objective (x y : ℝ) := x - 2 * y

/-- Find the maximum and minimum values of the expression $x - 2y$,  given that $\left(x, y\right)$ are related by the equation $\sqrt {x - 2} + \sqrt {y - 3} = 3$.  For which $\left(x, y\right)$ are these values attained? -/
theorem Calculus_4203_1 (x y : ℝ) (hx : x ≥ 2) (hy : y ≥ 3)
: constraint x y → objective x y ∈ Icc (-22:ℝ) (5:ℝ) := by
  set a := √ (x - 2) with h_a_x
  set b := √ (y - 3) with h_b_y

  have h_x_a : x = a ^ 2 + 2 := by rw [sq_sqrt (by linarith), sub_add_cancel]
  have h_y_b : y = b ^ 2 + 3 := by rw [sq_sqrt (by linarith), sub_add_cancel]

  intro h_constraint
  rw [constraint, ← h_a_x, ← h_b_y] at h_constraint

  have h_b_a : b = 3 - a := Eq.symm (sub_eq_of_eq_add' (id (Eq.symm h_constraint)))

  -- range of a 
  have h_a : a ∈ Icc (0:ℝ) (3:ℝ) := by
    simp [sqrt_nonneg (x - 2)]
    linarith [h_b_a, sqrt_nonneg (y - 3)]

  -- Convert objective into a unary function of a
  set f := fun (x : ℝ) => (-1) * x ^ 2 + 12 * x + -22 with hf
  have h_obj_a : objective x y = f a := by
    rw [objective, h_x_a, h_y_b, h_b_a]
    ring_nf
  rw [h_obj_a]

  -- Show that objective is monotonic in the range of a
  set f' := deriv (fun (x:ℝ) => f x) with hf'
  have : ∀ x ∈ Icc 0 3, f' x ≥ 0 := by
    intro x hx
    rw [hf']
    rw [hf, l_deriv (-1) 12 (-22)];
    simp at hx
    simp; linarith

  have f_min : f 0 = -22 := by simp [f]
  have f_max : f 3 = 5 := by simp [f]; ring

  have f_mono (x₁ x₂ : ℝ) : x₁ ∈ Icc 0 3 → x₂ ∈ Icc 0 3 → x₁ ≤ x₂ → f x₁ ≤ f x₂ := by
    intro hx1 hx2 h0
    simp at hx1 hx2
    have h1 : x₂ - x₁ ≥ 0 := by linarith
    have h2 : x₂ + x₁ - 12 ≤ 0 := by linarith
    have h3 : f x₁ - f x₂ ≤ 0 := by
      rw [show f x₁ - f x₂ = (x₂ + x₁ - 12) * (x₂ - x₁) by simp [f]; ring]
      exact mul_nonpos_of_nonpos_of_nonneg h2 h1
    exact tsub_nonpos.mp h3


  -- Get the range of objective within the range of a
  have h_ge_min: ∀ x ∈ Icc 0 3, f x ≥ f 0 := by
    intro x h
    simp at h
    apply f_mono
    . simp      -- 0 ∈ Icc 0 3
    . exact h   -- x ∈ Icc 0 3
    . simp [h]  -- 0 ≤ x
  have h_le_max: ∀ x ∈ Icc 0 3, f x ≤ f 3 := by
    intro x h
    simp at h
    apply f_mono
    . exact h   -- x ∈ Icc 0 3
    . simp      -- 3 ∈ Icc 0 3
    . simp [h]  -- x ≤ 3
  simp
  constructor
  . rw [← f_min]; exact h_ge_min a h_a
  . rw [← f_max]; exact h_le_max a h_a

/-- the minimum value of $x - 2y$ is $-22$. -/
theorem Calculus_4203_2 : objective 2 12 = -22 := by
  simp [objective]
  norm_num
/-- the maximum value of $x - 2y$ is $5$. -/
theorem Calculus_4203_3 : objective 11 3 = 5 := by
  simp [objective]
  norm_num
