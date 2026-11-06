import Mathlib
open Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

lemma lemma_1 {m : ℕ} (h : m ≠ 0) : (m : ℂ) • (m • (1 : Matrix n n ℂ))⁻¹ = (1 : Matrix n n ℂ) := by
  let I := (1 : Matrix n n ℂ)
  have : Invertible (m • I)
  · apply (m • I).invertibleOfIsUnitDet
    rw [Matrix.det_smul_of_tower, Matrix.det_one, Nat.smul_one_eq_cast, isUnit_iff_ne_zero, Nat.cast_ne_zero]
    exact pow_ne_zero _ h
  rw [Nat.smul_one_eq_cast] at this ⊢
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  apply Matrix.mul_inv_of_invertible

/- 2. Let $A \in \mathcal{M}_{n}(\mathbb{C})$, with the property $\operatorname{det}\left(A+m I_{n}\right)=m^{n} \operatorname{det}\left(A+\frac{1}{m} I_{n}\right)$, for any $m \in\{1,2, \cdots, n+$ $1\}$, where $I_{n}$ is the identity matrix of order $n$. Show that $\operatorname{det}(A)=1$. -/
theorem algebra_118733 {A : Matrix n n ℂ} (hA : ∀ m ∈ Finset.Icc 1 (Fintype.card n + 1), (A + m • 1).det = m ^ (Fintype.card n) * (A + 1 / m • 1).det) :
    A.det = 1 := by
  -- Rearrange the condition given
  conv at hA => intro m hm; rhs; rw [←Matrix.det_smul _ (m : ℂ), smul_add, one_div, lemma_1 (by simp at hm; linarith)]
  -- Set up our polynomial and show it is at most degree n
  set f := ((X : ℂ[X]) • Matrix.map 1 C + A.map C).det - ((X : ℂ[X]) • A.map C + Matrix.map 1 C).det
  have hf_deg : f.natDegree ≤ Fintype.card n
  · trans max ((X : ℂ[X]) • Matrix.map 1 C + A.map C).det.natDegree ((X : ℂ[X]) • A.map C + Matrix.map 1 C).det.natDegree
    · unfold f
      exact natDegree_sub_le _ _
    apply Nat.max_le.mpr
    exact ⟨natDegree_det_X_add_C_le 1 A, natDegree_det_X_add_C_le A 1⟩
  -- If f = 0 then we're done by evaluating f 0
  by_cases hf : f = 0
  · unfold f at hf
    have := congrArg (eval 0) hf
    simp [Matrix.eval_det] at this
    rw [←@sub_left_inj _ _ 1, this, sub_self]
  push_neg at hf
  -- Otherwise, f has at most n roots since it's degree n
  have hfn : f.roots.toFinset.card ≤ Fintype.card n
  · trans f.roots.card
    exact Multiset.toFinset_card_le f.roots
    trans f.natDegree
    exact Polynomial.card_roots' f
    exact hf_deg
  -- But f also has the n+1 roots {1, 2, 3, ..., n+1} by construction
  let s : Finset ℕ := Finset.Icc 1 (Fintype.card n + 1)
  have hs : ∀ x, x ∈ s → (x : ℂ) ∈ f.roots.toFinset
  · intro x hx
    specialize hA x hx
    simp only [Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def]
    refine ⟨hf, ?_⟩
    simp only [map_zero, map_one, Matrix.map_one, eval_sub, Matrix.eval_det, map_natCast, map_add,
      matPolyEquiv_map_smul, map_X, mul_one, matPolyEquiv_map_C, eval_add, eval_X, eval_C, X_mul_C,
      eval_mul_X, eval_one, f]
    conv => arg 1; arg 1; rw [←Nat.smul_one_eq_cast, add_comm]
    conv => arg 1; arg 2; rw [←Nat.smul_one_eq_cast, mul_smul_one]
    rw [Nat.cast_smul_eq_nsmul] at hA
    rw [hA, sub_self]
  have : Fintype.card n + 1 ≤ f.roots.toFinset.card
  · rw [Finset.le_card_iff_exists_subset_card]
    use s.image (fun (m : ℕ) => (m : ℂ))
    constructor
    · intro m hm
      simp only [Finset.mem_image, f] at hm
      rcases hm with ⟨m', hmem, hm'⟩
      rw [←hm']
      exact hs m' hmem
    rw [Finset.card_image_of_injective]
    simp only [Nat.card_Icc, add_tsub_cancel_right, Nat.add_left_cancel_iff, s, f]
    exact CharZero.cast_injective
  -- Contradiction
  linarith