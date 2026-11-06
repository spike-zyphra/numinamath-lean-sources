import Mathlib

/- ## Problem 4

On the set of non-zero real numbers $\mathbb{R}^{*}$, the composition law "*" is defined by $a * b=\left\{\begin{array}{l}\frac{a}{b}, \text { if } a < b \\ \frac{b}{a}, \text { if } a > b\end{array} \quad \forall a, b \in \mathbb{R}^{*}\right.$

a) Prove that $\left(\mathbb{R}^{*}, *\right)$ is a non-commutative group.

b) Solve the equation $a * b * a=b,\left(a, b \in \mathbb{R}^{*}\right)$.

## Note

- Effective working time 3 hours.
- All problems are mandatory.
- 7 points are awarded for each correctly solved problem.

## National Mathematics Olympiad  Local stage -14.02.2015  12th grade M $\mathbf{M}_{1}$ Solutions and marking schemes -/

-- Define the structure
structure R where
  x : ℝ
  h : x ≠ 0

-- Define the multiplication
noncomputable instance : Mul R where
  mul := fun a b =>
    if a.x > 0 then { x := a.x * b.x, h := mul_ne_zero a.h b.h }
    else { x := a.x / b.x, h := div_ne_zero a.h b.h }

@[simp]
theorem mul_def (a b : R) :
  a * b = if a.x > 0 then { x := a.x * b.x, h := mul_ne_zero a.h b.h }
    else { x := a.x / b.x, h := div_ne_zero a.h b.h } := rfl

-- Define the identity
instance : One R where
  one := { x := 1, h := zero_ne_one.symm }

@[simp]
theorem one_def : (1 : R) = { x := 1, h := zero_ne_one.symm } := rfl

-- Define the inverse
noncomputable instance : Inv R where
  inv := fun {x, h} => {
    x := if x > 0 then 1 / x else x,
    h := by by_cases hx : x > 0; repeat simp [h, hx] }

@[simp]
theorem inv_def (a : R):
/- Notice that the definition of inversion is reducible -/
  a⁻¹ = { x := if a.x > 0 then 1 / a.x else a.x, h := by by_cases hx : a.x > 0; repeat simp [a.h, hx] } := rfl

noncomputable instance: Group R := by
  apply Group.ofLeftAxioms
  -- show * is associative by cases on the sign of a, b
  case assoc =>
    intro a b c
    simp [mul_def]
    by_cases ha : a.x > 0
    · by_cases hb : b.x > 0
      · simp [ha, hb]
        exact mul_assoc a.x b.x c.x
      · simp [ha, hb]
        exact mul_div_assoc a.x b.x c.x
    · by_cases hb : b.x > 0
      · simp [ha, hb]
        exact div_div a.x b.x c.x
      · simp [ha, hb,
          div_pos_of_neg_of_neg ((not_lt.mp ha).lt_of_ne a.h) ((not_lt.mp hb).lt_of_ne b.h)]
        exact div_mul a.x b.x c.x
  -- show that 1 is indeed the identity
  case one_mul => intro a; simp

  -- show the inverse is indeed the inverse
  case inv_mul_cancel =>
    intro a
    simp
    by_cases ha : a.x > 0
    · simp [ha]
      exact inv_mul_cancel₀ a.h
    · simp [ha]
      exact div_self a.h

theorem problem_104216 : ∃ (a b : R), a * b ≠ b * a := ⟨
  -- show directly R is not commutative
  { x := 2, h := by norm_num },
  { x := -5, h := by norm_num },
  by rw [mul_def]; norm_num⟩