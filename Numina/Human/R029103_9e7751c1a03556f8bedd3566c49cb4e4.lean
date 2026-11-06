import Mathlib

/- What is the greatest possible quotient of any two distinct members of the set $\{\frac{2}{5}, \frac{1}{2},5,10\}$?  Specifically, we wish to maximize $\frac{x}{y}$, where $x$ and $y$ are chosen from the previous set. -/
theorem algebra_21643 (s : Finset ℝ) (h₀ : s = {2/5, 1/2, 5, 10}) :
    IsGreatest {x | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ x = a / b} (25) := by 
  rw [h₀]
  refine' ⟨by norm_num [div_eq_inv_mul], fun x hx => _⟩
  simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton,
    exists_imp, exists_eq_left] at hx
  rcases hx with ⟨a, rfl | rfl | rfl | rfl, b, rfl | rfl | rfl | rfl, hb⟩ <;>
    norm_num [div_eq_inv_mul] at hb ⊢
  <;> linarith