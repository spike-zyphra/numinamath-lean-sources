import Mathlib
set_option maxRecDepth 10000

/-- Given 1980 vectors in the plane, the sum of every 1979 vectors is a multiple of the remaining vector. Not all the vectors are multiples of each other. Show that the sum of all the vectors is zero.-/
theorem linear_algebra_4232 (x : Fin 1980 → Fin 2 → ℝ)
(ha : ∃ k : Fin 1980 → ℝ , ∀ j : Fin 1980,
(Finset.sum (Finset.univ \ {j}) fun i => x i) = k j • x j)
(nmul : ∃ i j, ∀ b : ℝ, x i ≠ b • x j) :
Finset.sum Finset.univ (fun i => x i) = 0 := by
rcases ha with ⟨k, hk⟩
rcases nmul with ⟨u, v, nuv⟩
-- Define the sum of all vectors.
let S := Finset.sum Finset.univ (fun i => x i)
-- Rearranging the above equation, we get $S = (k_i + 1)x_i$
have t1 : ∀ j, S = (k j + 1) • x j := by
  intro j; rw [add_smul, symm (hk j), one_smul]
  have : j ∉ Finset.univ \ {j} := by simp
  rw [add_comm, ← Finset.sum_insert this]; simp only [S]
  apply Finset.sum_congr; rw [Finset.insert_eq]; simp
  intro x _; rfl
-- get the equation for $j = u$ and $j = v$
have tu := t1 u
have tv := t1 v
rw [tu] at tv
by_cases hc : k u + 1 ≠ 0
have : Invertible (k u + 1) := invertibleOfNonzero hc
apply smul_eq_iff_eq_invOf_smul.mp at tv
have t2 := nuv (⅟(k u + 1) • (k v + 1))
-- Contradiction with given information.
rw [smul_assoc] at t2; contradiction
push_neg at hc; rw [hc] at tu; simp at tu
simp only [S] at tu; exact tu