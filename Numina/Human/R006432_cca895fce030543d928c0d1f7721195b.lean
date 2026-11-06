import Mathlib
/-Theorem: Let $x$ be an integer from 1 to 9 and $y$ be an integer from 0 to 9. Find the number of pairs of integers $(A,B)$ such that $A,B \in \{0,1,\dots,9\}$ and the number $N = 1000x + 100A + 10B + y$ is divisible by $11$. Show that this number is 10 if $x=y$ and 9 if $x \ne y$.-/
theorem number_theory_637008 :
    ∀ x y : ℕ, x ∈ Finset.Icc 1 9 ∧ y ∈ Finset.Icc 0 9 → ((Finset.Icc 0 9 ×ˢ Finset.Icc 0 9).filter fun ⟨A, B⟩ => 11 ∣ 1000 * x + 100 * A + 10 * B + y).card = if x = y then 10 else 9 := by
  intro x y h
  rcases h with ⟨hx, hy⟩
  simp only [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  interval_cases x <;> interval_cases y <;> native_decide