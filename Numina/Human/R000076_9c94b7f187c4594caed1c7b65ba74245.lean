import Mathlib


/-- $V$ is an n-dimensional vector space. Can we find a linear map $\( A : V \rightarrow V \)$ with $\( n+1 \)$ eigenvectors, any $\( n \)$ of which are linearly independent, which is not a scalar multiple of the identity? -/
theorem linear_algebra_4231 (V : Type*)[AddCommGroup V][Module ℝ V][FiniteDimensional ℝ V]
(n : ℕ)(hn : n = Module.finrank ℝ V)(hn1 : 1 ≤ n)
(f : Fin (n + 1) → V)
(hf : ∀ s : Finset (Fin (n + 1)), s.card = n → LinearIndependent ℝ (fun (i : s) => f i))
(A : V →ₗ[ℝ] V)(hA : ∃ a : Fin (n + 1) → ℝ, ∀ i, A (f i) = a i • f i) :
∃ b : ℝ , ∀ v, A v = b • v := by
-- We want to show that A is a scalar multiple of the identity map
rcases hA with ⟨a, ha⟩
let sa := Finset.sum (Finset.univ) (fun i => a i)
-- Define S(j) as the set of indices excluding j
let S (j : Fin (n + 1)) := Finset.univ \ {j}
let b (j : Fin (n + 1)) := fun (i : S j) => f i

have nempt (j : Fin (n + 1)): Nonempty (S j) := by
  simp only [S]; simp
  by_cases hj : j ≠ 0
  use 0; push_neg; symm; exact hj
  push_neg at hj; use 1; rw [hj]; push_neg; norm_num
  push_neg; linarith
-- Show that the cardinality of S(j) is n
have y1 : ∀ j, (S j).card = n := by
  intro j; simp only [S]; rw [Finset.card_univ_diff]; simp

have t1 : ∀ j, LinearIndependent ℝ (b j) := by
  intro j; simp only [b]; exact hf (S j) (y1 j)
-- Show that the span of b j covers the entire vector space V
have t2 : ∀ j, ⊤ ≤ Submodule.span ℝ (Set.range (b j)) := by
  intro j; simp
  apply LinearIndependent.span_eq_top_of_card_eq_finrank; exact t1 j
  rw [← hn]; simp; exact y1 j

let r2 (j : Fin (n + 1)) := Basis.mk (t1 j) (t2 j)

have r3 : ∀ j, LinearMap.traceAux ℝ (r2 j) A = sa - a j := by
  intro j; rw [LinearMap.traceAux_def]
  let matA := (LinearMap.toMatrix (r2 j) (r2 j)) A
  have diag : ∀ k, Matrix.diag matA k = a k := by
    intro k; rw [Matrix.diag]; dsimp [matA]
    rw [LinearMap.toMatrix_apply]
    have : (r2 j) k = f k := by
      simp only [r2]
      have x1 : b j k = f k := by simp only [b]
      have x2 := Basis.mk_apply (t1 j) (t2 j) k
      rw [← x1]; exact x2
    rw [this, ha k]; simp; rw [← this, Basis.repr_self]; simp
  rw [Matrix.trace]; simp only [diag]; simp; simp only [S]
  have : j ∉ Finset.univ \ {j} := by simp
  rw [Finset.sum_attach, eq_sub_iff_add_eq, add_comm, ← Finset.sum_insert this]
  simp only [sa]; apply Finset.sum_congr
  rw [Finset.insert_eq]; simp
  intro x _; rfl

have r4 : ∀ i j, a i = a j := by
  intro i j
  have q1i := r3 i
  have q1j := r3 j
  have q2 : LinearMap.traceAux ℝ (r2 i) = LinearMap.traceAux ℝ (r2 j) := LinearMap.traceAux_eq ℝ (r2 i) (r2 j)
  rw [q2, q1j] at q1i; simp at q1i; exact symm q1i

use a 1; intro v
rw [← Basis.sum_repr (r2 1) v, Finset.smul_sum]; simp
apply Finset.sum_congr; rfl; intro w _
by_cases h' : ((r2 1).repr v) w = 0
rw [h']; simp
push_neg at h'; rw [smul_comm, IsUnit.smul_left_cancel]
have hw := w.2
have : (r2 1) w = f w := by
  simp only [r2]
  have x1 : b 1 w = f w := by simp only [b]
  have x2 := Basis.mk_apply (t1 1) (t2 1) w
  rw [← x1]; exact x2
simp only [S] at hw; simp at hw
rw [this, r4 1 w]; exact ha w
apply isUnit_iff_ne_zero.mpr; exact h'
