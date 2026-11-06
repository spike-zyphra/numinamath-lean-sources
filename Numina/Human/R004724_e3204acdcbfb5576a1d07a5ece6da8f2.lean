import Mathlib
open Real

-- Define the constraints for the sides of a triangle.
def is_triangle (a b c : ℝ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a

/-4. Given the three sides of $\triangle A B C$ are $a, b, c$, and
$$
\frac{a}{b}+\frac{a}{c}=\frac{b+c}{b+c-a} \text {. }
$$
Then the triangle that satisfies this condition is ( )
(A) equilateral triangle
(B) isosceles triangle with $a$ as the leg
(C) isosceles triangle with $a$ as the base
(D) isosceles right triangle-/
theorem algebra_20002 (a b c : ℝ) (h_tri : is_triangle a b c)
    (h_eq : a / b + a / c = (b + c) / (b + c - a)) :
    b = a ∨ c = a := by
  -- Prove that the denominator $b * c$ is greater than $0$.
  have h_bc_pos : b * c > 0 := by
      apply mul_pos
      exact h_tri.2.1
      exact h_tri.2.2.1
  -- Simplify the equation to $a(b + c) / (b * c) = (b + c) / (b + c - a)$.
  have h_simplify : a * (b + c) / (b * c) = (b + c) / (b + c - a) := by
    have h_right : a / b + a / c = a * (b + c) / (b * c) := by
      calc
        a / b + a / c = (a * c) / (b * c) + (a * b) / (b * c) := by
          have : a / b = (a * c) / (b * c) := by
            rw [← mul_div_mul_right]
            nlinarith [h_tri.2.2.1]
          have : a / c = (a * b) / (b * c) := by
            rw [mul_comm b c,← mul_div_mul_right]
            nlinarith [h_tri.2.1]
          linarith
        _ = (a * c + a * b) / (b * c) := by
          rw [add_div]
        _ = a * (b + c) / (b * c) := by
          rw [← mul_add, add_comm]
    rwa [h_right] at h_eq
  -- Eliminate the denominator to obtain $a * (b + c) * (b + c - a) = (b * c) * (b + c)$.
  have h_cross : a * (b + c) * (b + c - a) = b * c * (b + c) := by
    -- Multiply both sides by $(b * c) * (b + c - a)$.
    have h_bc_pos : b * c ≠ 0 := by nlinarith
    have h_b_c_a_pos : b + c - a ≠ 0 := by
      have : b + c > a := h_tri.2.2.2.2.2
      linarith
    have h_denom : (b * c) * (b + c - a) ≠ 0 := by
      apply mul_ne_zero
      exact h_bc_pos
      exact h_b_c_a_pos
    -- Multiply both sides by $(b * c) * (b + c - a)$.
    calc
      a * (b + c) * (b + c - a) = (a * (b + c) / (b * c)) * ((b * c) * (b + c - a)) := by
        rw [div_mul_eq_mul_div]
        rw [mul_comm (b * c), mul_assoc]
        rw [mul_div_assoc]
        field_simp
        ring_nf
      _ = ((b + c) / (b + c - a)) * ((b * c) * (b + c - a)) := by
        rw [h_simplify]
      _ = b * c * (b + c) := by
        rw [div_mul_eq_mul_div]
        rw [mul_assoc]
        field_simp
        ring_nf
  -- Simplify to $(b + c) * (b - a) * (c - a) = 0$.
  have h_factor : (b + c) * (b - a) * (c - a) = 0 := by
    calc
      (b + c) * (b - a) * (c - a) =  b * c * (b + c) - a * (b + c) * (b + c - a) := by
        ring_nf
      _ = 0 := by rw [h_cross]; ring
  -- Use $b + c > 0$ to deduce $b - a = 0$ or $c - a = 0$.
  have h_b_p_c_pos : b + c ≠  0 := by linarith [h_tri.2.1, h_tri.2.2.1]
  have h_cases : b - a = 0 ∨ c - a = 0 := by
    have : (b - a) * (c - a) = 0 := by
      apply (mul_eq_zero_iff_left h_b_p_c_pos).mp
      rw [mul_assoc] at h_factor
      exact h_factor
    exact mul_eq_zero.mp this
  -- Conclude $b = a$ or $c = a$.
  exact Or.imp (fun h : b - a = 0 => sub_eq_zero.mp h) (fun h : c - a = 0 => sub_eq_zero.mp h) h_cases
