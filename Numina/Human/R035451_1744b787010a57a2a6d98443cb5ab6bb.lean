import Mathlib

/-- Let $\left(u_{n}\right)_{n \in \mathbb{N}}$ be a periodic sequence of period 2022 and period 5. Show that $\left(u_{n}\right)$ is constant. -/
theorem number_theory_607363 (u : ℕ → ℝ) (h : Function.Periodic u 2022) (h' : Function.Periodic u 5) :
    ∃ c, ∀ n, u n = c := by
  have (k : ℕ) : u (k + 1) = u k := calc
    -- Use the periodicity of `u` with period 2022.
    _ = u (k + 1 + (2 : ℕ) * 2022) := by
      rw [← Function.Periodic.nat_mul h 2 (k + 1)]
      rfl
    _ = u (k + 5 * 809) := by
      norm_num
    -- Use the periodicity of `u` with period 5.
    _ = u k := by
      rw [← Function.Periodic.nat_mul h' 809 k]
      rfl
  -- Choose `c` as the first value in the sequence
  use u 0
  -- Complete the proof by induction using what we just proved
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [this n, ih]
