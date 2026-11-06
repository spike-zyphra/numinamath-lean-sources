import Mathlib

open Nat Rat

/- Compute

$$
\left\lfloor\frac{2007!+2004!}{2006!+2005!}\right\rfloor
$$

(Note that $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x$.) -/
theorem algrebra_608132
    : ((2027!+2024!)/(2026!+2025!): ℚ).floor = 2026 := by
    -- rewrite both numerator and denominator into multiple of 2024!
    rw [factorial_succ 2026, factorial_succ 2025, factorial_succ 2024] ; simp
    repeat rw [← mul_assoc]

    -- reduction with 2024!
    nth_rewrite 2 [← one_mul (2024!: ℚ)] ; repeat rw [← add_mul (c:= (2024!: ℚ))]
    rw [mul_div_mul_right] ; all_goals try positivity

    -- compute rest of the expression
    norm_num [Nat.floor_eq_iff, Nat.div_eq_of_lt, Rat.floor]
