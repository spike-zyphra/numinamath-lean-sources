import Mathlib


/-Solve for $z$ in the following equation: $1-iz = -1 + iz$ (where $i^2 = -1$). Simplify your answer as much as possible.-/
theorem algebra_10554 {z : ℂ} (hz : 1 - Complex.I * z = -1 + Complex.I * z) : z = -Complex.I := by
  -- $1 - iz = -1 + iz \Rightarrow 2 = 2iz
  rw [add_comm, add_neg_eq_iff_eq_add.symm, add_comm, add_sub] at hz
  simp at hz
  rw [one_add_one_eq_two, sub_eq_iff_eq_add, ←mul_two] at hz
  -- \Rightarrow z = \frac{1}{i}$.
  simp at hz
  rw [Eq.comm, mul_comm] at hz
  apply (div_eq_iff (by norm_num: Complex.I ≠ 0)).mpr at hz
  -- Multiplying the numerator and denominator by $-i$, we get $z = \frac{1}{i} \cdot \frac{-i}{-i} = \frac{-i}{1} = \boxed{-i}$.
  rw [Eq.comm, (by norm_num : -Complex.I / -Complex.I = 1).symm] at hz
  simp at hz
  exact hz
