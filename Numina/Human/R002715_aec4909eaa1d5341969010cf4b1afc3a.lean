import Mathlib

/- ## SUBJECT 2

Let $A, B \in \mathrm{M}_{2}(R)$ with the property that $\operatorname{Tr}\left(A^{2} B^{2}\right)=(\operatorname{Tr}(A B))^{2}$. Show that $\operatorname{det}(A B - B A) = 2 \cdot \operatorname{det} A \cdot \operatorname{det} B$. (We have denoted by $\operatorname{Tr}(\mathrm{X})$ the trace of matrix X)

prof. Cătălin Zîrnă -/
lemma lemma_1 (C : Matrix (Fin 2) (Fin 2) ℝ) : C.det • 1 + -C.trace • C + C ^ 2 = 0 := by
  -- show Cayley-Hamilton takes a simple form in the case n = 2
  rw [←Matrix.aeval_self_charpoly C]
  have hc2 := Polynomial.Monic.coeff_natDegree (Matrix.charpoly_monic C)
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hc2
  have hc1 : C.charpoly.coeff (Fintype.card (Fin 2) - 1) = -C.trace
  · rw [←neg_eq_iff_eq_neg, ←Matrix.trace_eq_neg_charpoly_coeff]
  rw [Fintype.card_fin, show 2 - 1 = 1 by rfl] at hc1
  have hc0 : C.charpoly.coeff 0 = C.det
  · rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
    simp only [even_two, Even.neg_pow, one_pow, one_mul]
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, zero_add, pow_one, pow_zero,
    hc0, hc1, hc2, one_smul]

lemma lemma_2 {A B : Matrix (Fin 2) (Fin 2) ℝ} : ((A * B - B * A)^2).trace = 2 * ((A * B)^2).trace - 2 * (A^2 * B^2).trace := by calc
  _ = ((A * B) * (A * B)).trace - ((A * B) * (B * A)).trace - ((B * A) * (A * B)).trace + ((B * A) * (B * A)).trace := by
    rw [sq, sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm]
    ring
  _ = ((A * B)^2).trace - (A * B * B * A).trace - (B * (A * A * B)).trace + (B * ((A * B) * A)).trace := by noncomm_ring
  _ = ((A * B) ^ 2).trace - ((A * A) * (B * B)).trace - ((A * A) * (B * B)).trace + ((A * B * A) * B).trace := by
    rw [Matrix.trace_mul_comm _ A, Matrix.trace_mul_comm B _, Matrix.trace_mul_comm B _]
    noncomm_ring
  _ = 2 * ((A * B) ^ 2).trace - 2 * (A ^ 2 * B ^ 2).trace := by noncomm_ring

theorem algebra_103290 {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (A ^ 2 * B ^ 2).trace = (A * B).trace ^ 2) :
    (A * B - B * A).det = 2 * A.det * B.det := by
  -- Define C := A * B - B * A and apply Cayley-Hamilton
  let C := A * B - B * A
  have hc := lemma_1 C
  have c_tr : -C.trace = 0
  · simp [C]
    rw [sub_eq_zero, Matrix.trace_mul_comm]
  rw [c_tr, zero_smul, add_zero] at hc
  -- Take the trace of the Cayley-Hamilton equation satisfied by C
  have hc_tr := congrArg Matrix.trace hc
  simp [C, lemma_2] at hc_tr
  have hc_tr' : (A * B - B * A).det =  (A ^ 2 * B ^ 2).trace - ((A * B) ^ 2).trace
  · linarith
  -- Do the same for D := A * B and conclude
  let D := A * B
  have hd_tr := congrArg Matrix.trace (lemma_1 D)
  simp [D] at hd_tr
  linarith